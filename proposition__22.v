Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7a.
Require Export lemma__3__7b.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__layoff.
Require Export lemma__layoffunique.
Require Export lemma__lessthancongruence.
Require Export lemma__lessthancongruence2.
Require Export lemma__lessthannotequal.
Require Export lemma__ondiameter.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__subtractequals.
Require Export lemma__together.
Require Export lemma__trichotomy2.
Require Export logic.
Definition lemma__togethera : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.TG A a B b C c) -> ((euclidean__axioms.Cong D F A a) -> ((euclidean__axioms.Cong F G B b) -> ((euclidean__axioms.BetS D F G) -> ((euclidean__axioms.Cong P Q C c) -> (euclidean__defs.Lt P Q D G))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro F.
intro G.
intro P.
intro Q.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) ((euclidean__defs.TG A a B b C c) -> ((euclidean__axioms.Cong D F A a) -> ((euclidean__axioms.Cong F G B b) -> ((euclidean__axioms.BetS D F G) -> ((euclidean__axioms.Cong P Q C c) -> (euclidean__defs.Lt P Q D G)))))) as H4.
- intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.Lt P Q D G) /\ ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq B b) /\ (euclidean__axioms.neq C c)))) as __4.
-- apply (@lemma__together.lemma__together (A) (B) (C) (D) (F) (G) (P) (Q) (a) (b) (c) (__) (__0) (__1) (__2) __3).
-- destruct __4 as [__4 __5].
exact __4.
- apply (@H4 (H) (H0) (H1) (H2) H3).
Qed.
Definition proposition__22 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.TG A a B b C c) -> ((euclidean__defs.TG A a C c B b) -> ((euclidean__defs.TG B b C c A a) -> ((euclidean__axioms.neq F E) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point), (euclidean__axioms.Cong F X B b) /\ ((euclidean__axioms.Cong F Y A a) /\ ((euclidean__axioms.Cong X Y C c) /\ ((euclidean__defs.Out F E X) /\ (euclidean__axioms.Triangle F X Y)))))))).
Proof.
intro A.
intro B.
intro C.
intro E.
intro F.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS A a P) /\ ((euclidean__axioms.Cong a P B b) /\ (euclidean__defs.Lt C c A P))) as H3.
- exact H.
- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS A a P) /\ ((euclidean__axioms.Cong a P B b) /\ (euclidean__defs.Lt C c A P)))) as H4.
-- exact H3.
-- destruct H4 as [P H4].
assert (* AndElim *) ((euclidean__axioms.BetS A a P) /\ ((euclidean__axioms.Cong a P B b) /\ (euclidean__defs.Lt C c A P))) as H5.
--- exact H4.
--- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Cong a P B b) /\ (euclidean__defs.Lt C c A P)) as H7.
---- exact H6.
---- destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.neq A a) as H9.
----- assert (* Cut *) ((euclidean__axioms.neq a P) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A P))) as H9.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (P) H5).
------ assert (* AndElim *) ((euclidean__axioms.neq a P) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A P))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A P)) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
exact H12.
----- assert (* Cut *) (euclidean__axioms.neq a P) as H10.
------ assert (* Cut *) ((euclidean__axioms.neq a P) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A P))) as H10.
------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (a) (P) H5).
------- assert (* AndElim *) ((euclidean__axioms.neq a P) /\ ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A P))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ (euclidean__axioms.neq A P)) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
exact H11.
------ assert (* Cut *) (euclidean__axioms.neq B b) as H11.
------- apply (@euclidean__axioms.axiom__nocollapse (a) (P) (B) (b) (H10) H7).
------- assert (* Cut *) (euclidean__axioms.neq C c) as H12.
-------- assert (* Cut *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq A P)) as H12.
--------- apply (@lemma__lessthannotequal.lemma__lessthannotequal (C) (c) (A) (P) H8).
--------- assert (* AndElim *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq A P)) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
exact H13.
-------- assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__defs.Out F E G) /\ (euclidean__axioms.Cong F G B b)) as H13.
--------- apply (@lemma__layoff.lemma__layoff (F) (E) (B) (b) (H2) H11).
--------- assert (exists G: euclidean__axioms.Point, ((euclidean__defs.Out F E G) /\ (euclidean__axioms.Cong F G B b))) as H14.
---------- exact H13.
---------- destruct H14 as [G H14].
assert (* AndElim *) ((euclidean__defs.Out F E G) /\ (euclidean__axioms.Cong F G B b)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* Cut *) (euclidean__axioms.Cong B b F G) as H17.
------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (F) (G) (b) H16).
------------ assert (* Cut *) (euclidean__axioms.neq F G) as H18.
------------- apply (@euclidean__axioms.axiom__nocollapse (B) (b) (F) (G) (H11) H17).
------------- assert (* Cut *) (euclidean__axioms.neq G F) as H19.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (G) H18).
-------------- assert (* Cut *) (exists (H20: euclidean__axioms.Point), (euclidean__axioms.BetS F G H20) /\ (euclidean__axioms.Cong G H20 C c)) as H20.
--------------- apply (@lemma__extension.lemma__extension (F) (G) (C) (c) (H18) H12).
--------------- assert (exists H21: euclidean__axioms.Point, ((euclidean__axioms.BetS F G H21) /\ (euclidean__axioms.Cong G H21 C c))) as H22.
---------------- exact H20.
---------------- destruct H22 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.BetS F G H21) /\ (euclidean__axioms.Cong G H21 C c)) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS G F D) /\ (euclidean__axioms.Cong F D A a)) as H25.
------------------ apply (@lemma__extension.lemma__extension (G) (F) (A) (a) (H19) H9).
------------------ assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS G F D) /\ (euclidean__axioms.Cong F D A a))) as H26.
------------------- exact H25.
------------------- destruct H26 as [D H26].
assert (* AndElim *) ((euclidean__axioms.BetS G F D) /\ (euclidean__axioms.Cong F D A a)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
assert (* Cut *) (euclidean__axioms.Cong D F A a) as H29.
--------------------- assert (* Cut *) ((euclidean__axioms.Cong D F a A) /\ ((euclidean__axioms.Cong D F A a) /\ (euclidean__axioms.Cong F D a A))) as H29.
---------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (D) (A) (a) H28).
---------------------- assert (* AndElim *) ((euclidean__axioms.Cong D F a A) /\ ((euclidean__axioms.Cong D F A a) /\ (euclidean__axioms.Cong F D a A))) as H30.
----------------------- exact H29.
----------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Cong D F A a) /\ (euclidean__axioms.Cong F D a A)) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [H32 H33].
exact H32.
--------------------- assert (* Cut *) (euclidean__axioms.BetS D F G) as H30.
---------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (F) (D) H27).
---------------------- assert (* Cut *) (euclidean__axioms.neq F D) as H31.
----------------------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq G F) /\ (euclidean__axioms.neq G D))) as H31.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (G) (F) (D) H27).
------------------------ assert (* AndElim *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq G F) /\ (euclidean__axioms.neq G D))) as H32.
------------------------- exact H31.
------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq G F) /\ (euclidean__axioms.neq G D)) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [H34 H35].
exact H32.
----------------------- assert (* Cut *) (euclidean__axioms.neq G H21) as H32.
------------------------ assert (* Cut *) ((euclidean__axioms.neq G H21) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq F H21))) as H32.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (G) (H21) H23).
------------------------- assert (* AndElim *) ((euclidean__axioms.neq G H21) /\ ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq F H21))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq F G) /\ (euclidean__axioms.neq F H21)) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
exact H33.
------------------------ assert (* Cut *) (exists (L: euclidean__axioms.Circle), euclidean__axioms.CI L F F D) as H33.
------------------------- apply (@euclidean__axioms.postulate__Euclid3 (F) (D) H31).
------------------------- assert (exists L: euclidean__axioms.Circle, (euclidean__axioms.CI L F F D)) as H34.
-------------------------- exact H33.
-------------------------- destruct H34 as [L H34].
assert (* Cut *) (exists (R: euclidean__axioms.Circle), euclidean__axioms.CI R G G H21) as H35.
--------------------------- apply (@euclidean__axioms.postulate__Euclid3 (G) (H21) H32).
--------------------------- assert (exists R: euclidean__axioms.Circle, (euclidean__axioms.CI R G G H21)) as H36.
---------------------------- exact H35.
---------------------------- destruct H36 as [R H36].
assert (* Cut *) (euclidean__axioms.Cong G H21 G H21) as H37.
----------------------------- apply (@euclidean__axioms.cn__congruencereflexive (G) H21).
----------------------------- assert (* Cut *) (euclidean__axioms.OnCirc H21 R) as H38.
------------------------------ exists G.
exists H21.
exists G.
split.
------------------------------- exact H36.
------------------------------- exact H37.
------------------------------ assert (* Cut *) (euclidean__defs.Lt D F F H21) as H39.
------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point) (F0: euclidean__axioms.Point) (G0: euclidean__axioms.Point) (P0: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (a0: euclidean__axioms.Point) (b0: euclidean__axioms.Point) (c0: euclidean__axioms.Point), (euclidean__defs.TG A0 a0 B0 b0 C0 c0) -> ((euclidean__axioms.Cong D0 F0 A0 a0) -> ((euclidean__axioms.Cong F0 G0 B0 b0) -> ((euclidean__axioms.BetS D0 F0 G0) -> ((euclidean__axioms.Cong P0 Q C0 c0) -> (euclidean__defs.Lt P0 Q D0 G0)))))) as H39.
-------------------------------- intro A0.
intro B0.
intro C0.
intro D0.
intro F0.
intro G0.
intro P0.
intro Q.
intro a0.
intro b0.
intro c0.
intro __.
intro __0.
intro __1.
intro __2.
intro __3.
assert (* AndElim *) ((euclidean__defs.Lt P0 Q D0 G0) /\ ((euclidean__axioms.neq A0 a0) /\ ((euclidean__axioms.neq B0 b0) /\ (euclidean__axioms.neq C0 c0)))) as __4.
--------------------------------- apply (@lemma__together.lemma__together (A0) (B0) (C0) (D0) (F0) (G0) (P0) (Q) (a0) (b0) (c0) (__) (__0) (__1) (__2) __3).
--------------------------------- destruct __4 as [__4 __5].
exact __4.
-------------------------------- apply (@H39 (B) (C) (A) (F) (G) (H21) (D) (F) (b) (c) (a) (H1) (H16) (H24) (H23) H29).
------------------------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS F M H21) /\ (euclidean__axioms.Cong F M D F)) as H40.
-------------------------------- exact H39.
-------------------------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS F M H21) /\ (euclidean__axioms.Cong F M D F))) as H41.
--------------------------------- exact H40.
--------------------------------- destruct H41 as [M H41].
assert (* AndElim *) ((euclidean__axioms.BetS F M H21) /\ (euclidean__axioms.Cong F M D F)) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) (euclidean__axioms.Cong F M A a) as H44.
----------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (M) (D) (F) (A) (a) (H43) H29).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong A a F M) as H45.
------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (F) (M) (a) H44).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong A a F D) as H46.
------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (F) (D) (a) H28).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F M F D) as H47.
-------------------------------------- apply (@euclidean__axioms.cn__congruencetransitive (F) (M) (F) (D) (A) (a) (H45) H46).
-------------------------------------- assert (* Cut *) (euclidean__axioms.OutCirc H21 L) as H48.
--------------------------------------- exists M.
exists F.
exists F.
exists D.
split.
---------------------------------------- exact H34.
---------------------------------------- split.
----------------------------------------- exact H42.
----------------------------------------- exact H47.
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C c C c) as H49.
---------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (C) c).
---------------------------------------- assert (* Cut *) (euclidean__defs.Lt C c D G) as H50.
----------------------------------------- apply (@proposition__22.lemma__togethera (A) (B) (C) (D) (F) (G) (C) (c) (a) (b) (c) (H) (H29) (H16) (H30) H49).
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong D G G D) as H51.
------------------------------------------ apply (@euclidean__axioms.cn__equalityreverse (D) G).
------------------------------------------ assert (* Cut *) (euclidean__defs.Lt C c G D) as H52.
------------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (c) (D) (G) (G) (D) (H50) H51).
------------------------------------------- assert (* Cut *) (exists (N: euclidean__axioms.Point), (euclidean__axioms.BetS G N D) /\ (euclidean__axioms.Cong G N C c)) as H53.
-------------------------------------------- exact H52.
-------------------------------------------- assert (exists N: euclidean__axioms.Point, ((euclidean__axioms.BetS G N D) /\ (euclidean__axioms.Cong G N C c))) as H54.
--------------------------------------------- exact H53.
--------------------------------------------- destruct H54 as [N H54].
assert (* AndElim *) ((euclidean__axioms.BetS G N D) /\ (euclidean__axioms.Cong G N C c)) as H55.
---------------------------------------------- exact H54.
---------------------------------------------- destruct H55 as [H55 H56].
assert (* Cut *) (euclidean__axioms.BetS D F H21) as H57.
----------------------------------------------- apply (@lemma__3__7b.lemma__3__7b (D) (F) (G) (H21) (H30) H23).
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D F M) as H58.
------------------------------------------------ apply (@euclidean__axioms.axiom__innertransitivity (D) (F) (M) (H21) (H57) H42).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong F D A a) as H59.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong N G c C) /\ ((euclidean__axioms.Cong N G C c) /\ (euclidean__axioms.Cong G N c C))) as H59.
-------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (G) (N) (C) (c) H56).
-------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong N G c C) /\ ((euclidean__axioms.Cong N G C c) /\ (euclidean__axioms.Cong G N c C))) as H60.
--------------------------------------------------- exact H59.
--------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Cong N G C c) /\ (euclidean__axioms.Cong G N c C)) as H62.
---------------------------------------------------- exact H61.
---------------------------------------------------- destruct H62 as [H62 H63].
exact H28.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D N G) as H60.
-------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (N) (D) H55).
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F M) as H61.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D M))) as H61.
---------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (D) (F) (M) H58).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D M))) as H62.
----------------------------------------------------- exact H61.
----------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.neq D F) /\ (euclidean__axioms.neq D M)) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
exact H62.
--------------------------------------------------- assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS F M J) /\ (euclidean__axioms.Cong M J C c)) as H62.
---------------------------------------------------- apply (@lemma__extension.lemma__extension (F) (M) (C) (c) (H61) H12).
---------------------------------------------------- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS F M J) /\ (euclidean__axioms.Cong M J C c))) as H63.
----------------------------------------------------- exact H62.
----------------------------------------------------- destruct H63 as [J H63].
assert (* AndElim *) ((euclidean__axioms.BetS F M J) /\ (euclidean__axioms.Cong M J C c)) as H64.
------------------------------------------------------ exact H63.
------------------------------------------------------ destruct H64 as [H64 H65].
assert (* Cut *) (euclidean__axioms.BetS D F J) as H66.
------------------------------------------------------- apply (@lemma__3__7b.lemma__3__7b (D) (F) (M) (J) (H58) H64).
------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Lt F G F J) /\ ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b)))) as H67.
-------------------------------------------------------- apply (@lemma__together.lemma__together (A) (C) (B) (F) (M) (J) (F) (G) (a) (c) (b) (H0) (H44) (H65) (H64) H16).
-------------------------------------------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS F Q J) /\ (euclidean__axioms.Cong F Q F G)) as H68.
--------------------------------------------------------- assert (* AndElim *) ((exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS F X J) /\ (euclidean__axioms.Cong F X F G)) /\ ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b)))) as H68.
---------------------------------------------------------- exact H67.
---------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b))) as H70.
----------------------------------------------------------- exact H69.
----------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b)) as H72.
------------------------------------------------------------ exact H71.
------------------------------------------------------------ destruct H72 as [H72 H73].
exact H68.
--------------------------------------------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS F Q J) /\ (euclidean__axioms.Cong F Q F G))) as H69.
---------------------------------------------------------- exact H68.
---------------------------------------------------------- destruct H69 as [Q H69].
assert (* AndElim *) ((euclidean__axioms.BetS F Q J) /\ (euclidean__axioms.Cong F Q F G)) as H70.
----------------------------------------------------------- exact H69.
----------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__defs.Lt F G F J) /\ ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b)))) as H72.
------------------------------------------------------------ exact H67.
------------------------------------------------------------ destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.neq A a) /\ ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b))) as H74.
------------------------------------------------------------- exact H73.
------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.neq C c) /\ (euclidean__axioms.neq B b)) as H76.
-------------------------------------------------------------- exact H75.
-------------------------------------------------------------- destruct H76 as [H76 H77].
assert (* Cut *) (euclidean__axioms.neq F J) as H78.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq Q J) /\ ((euclidean__axioms.neq F Q) /\ (euclidean__axioms.neq F J))) as H78.
---------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (Q) (J) H70).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq Q J) /\ ((euclidean__axioms.neq F Q) /\ (euclidean__axioms.neq F J))) as H79.
----------------------------------------------------------------- exact H78.
----------------------------------------------------------------- destruct H79 as [H79 H80].
assert (* AndElim *) ((euclidean__axioms.neq F Q) /\ (euclidean__axioms.neq F J)) as H81.
------------------------------------------------------------------ exact H80.
------------------------------------------------------------------ destruct H81 as [H81 H82].
exact H82.
--------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out F J Q) as H79.
---------------------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (F) (J) (Q)).
-----------------------------------------------------------------left.
exact H70.

----------------------------------------------------------------- exact H78.
---------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out F G J) as H80.
----------------------------------------------------------------- exists D.
split.
------------------------------------------------------------------ exact H66.
------------------------------------------------------------------ exact H30.
----------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Out F J G) as H81.
------------------------------------------------------------------ apply (@lemma__ray5.lemma__ray5 (F) (G) (J) H80).
------------------------------------------------------------------ assert (* Cut *) (Q = G) as H82.
------------------------------------------------------------------- apply (@lemma__layoffunique.lemma__layoffunique (F) (J) (Q) (G) (H79) (H81) H71).
------------------------------------------------------------------- assert (* Cut *) (G = Q) as H83.
-------------------------------------------------------------------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (G) (Q) H82).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS F G J) as H84.
--------------------------------------------------------------------- apply (@eq__ind euclidean__axioms.Point Q (fun G0: euclidean__axioms.Point => (euclidean__defs.Out F E G0) -> ((euclidean__axioms.Cong F G0 B b) -> ((euclidean__axioms.Cong B b F G0) -> ((euclidean__axioms.neq F G0) -> ((euclidean__axioms.neq G0 F) -> ((euclidean__axioms.BetS F G0 H21) -> ((euclidean__axioms.Cong G0 H21 C c) -> ((euclidean__axioms.BetS G0 F D) -> ((euclidean__axioms.BetS D F G0) -> ((euclidean__axioms.neq G0 H21) -> ((euclidean__axioms.CI R G0 G0 H21) -> ((euclidean__axioms.Cong G0 H21 G0 H21) -> ((euclidean__defs.Lt C c D G0) -> ((euclidean__axioms.Cong D G0 G0 D) -> ((euclidean__defs.Lt C c G0 D) -> ((euclidean__axioms.BetS G0 N D) -> ((euclidean__axioms.Cong G0 N C c) -> ((euclidean__axioms.BetS D N G0) -> ((euclidean__defs.Lt F G0 F J) -> ((euclidean__axioms.Cong F Q F G0) -> ((euclidean__defs.Out F G0 J) -> ((euclidean__defs.Out F J G0) -> ((G0 = Q) -> (euclidean__axioms.BetS F G0 J))))))))))))))))))))))))) with (y := G).
----------------------------------------------------------------------intro H84.
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
intro H105.
intro H106.
assert (* Cut *) (Q = Q) as H107.
----------------------------------------------------------------------- exact H106.
----------------------------------------------------------------------- exact H70.

---------------------------------------------------------------------- exact H82.
---------------------------------------------------------------------- exact H15.
---------------------------------------------------------------------- exact H16.
---------------------------------------------------------------------- exact H17.
---------------------------------------------------------------------- exact H18.
---------------------------------------------------------------------- exact H19.
---------------------------------------------------------------------- exact H23.
---------------------------------------------------------------------- exact H24.
---------------------------------------------------------------------- exact H27.
---------------------------------------------------------------------- exact H30.
---------------------------------------------------------------------- exact H32.
---------------------------------------------------------------------- exact H36.
---------------------------------------------------------------------- exact H37.
---------------------------------------------------------------------- exact H50.
---------------------------------------------------------------------- exact H51.
---------------------------------------------------------------------- exact H52.
---------------------------------------------------------------------- exact H55.
---------------------------------------------------------------------- exact H56.
---------------------------------------------------------------------- exact H60.
---------------------------------------------------------------------- exact H72.
---------------------------------------------------------------------- exact H71.
---------------------------------------------------------------------- exact H80.
---------------------------------------------------------------------- exact H81.
---------------------------------------------------------------------- exact H83.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D G J) as H85.
---------------------------------------------------------------------- apply (@lemma__3__7a.lemma__3__7a (D) (F) (G) (J) (H30) H84).
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C c M J) as H86.
----------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (M) (J) (c) H65).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G N M J) as H87.
------------------------------------------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (G) (N) (C) (c) (M) (J) (H56) H86).
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong N G M J) as H88.
------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong N G J M) /\ ((euclidean__axioms.Cong N G M J) /\ (euclidean__axioms.Cong G N J M))) as H88.
-------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (G) (N) (M) (J) H87).
-------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong N G J M) /\ ((euclidean__axioms.Cong N G M J) /\ (euclidean__axioms.Cong G N J M))) as H89.
--------------------------------------------------------------------------- exact H88.
--------------------------------------------------------------------------- destruct H89 as [H89 H90].
assert (* AndElim *) ((euclidean__axioms.Cong N G M J) /\ (euclidean__axioms.Cong G N J M)) as H91.
---------------------------------------------------------------------------- exact H90.
---------------------------------------------------------------------------- destruct H91 as [H91 H92].
exact H91.
------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D M J) as H89.
-------------------------------------------------------------------------- apply (@lemma__3__7a.lemma__3__7a (D) (F) (M) (J) (H58) H64).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS D N M) as H90.
--------------------------------------------------------------------------- apply (@lemma__subtractequals.lemma__subtractequals (D) (N) (G) (M) (J) (H60) (H89) (H88) H85).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F D F D) as H91.
---------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (F) D).
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.InCirc N L) as H92.
----------------------------------------------------------------------------- apply (@lemma__ondiameter.lemma__ondiameter (D) (F) (L) (M) (N) (F) (D) (H34) (H91) (H47) (H58) H90).
----------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C c G H21) as H93.
------------------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (G) (H21) (c) H24).
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong C c G N) as H94.
------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (G) (N) (c) H56).
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G N G H21) as H95.
-------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__congruencetransitive (G) (N) (G) (H21) (C) (c) (H94) H93).
-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.OnCirc N R) as H96.
--------------------------------------------------------------------------------- exists G.
exists H21.
exists G.
split.
---------------------------------------------------------------------------------- exact H36.
---------------------------------------------------------------------------------- exact H95.
--------------------------------------------------------------------------------- assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.OnCirc K L) /\ (euclidean__axioms.OnCirc K R)) as H97.
---------------------------------------------------------------------------------- apply (@euclidean__axioms.postulate__circle__circle (F) (G) (G) (H21) (L) (R) (N) (H21) (F) (D) (H34) (H92) (H48) (H36) (H96) H38).
---------------------------------------------------------------------------------- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.OnCirc K L) /\ (euclidean__axioms.OnCirc K R))) as H98.
----------------------------------------------------------------------------------- exact H97.
----------------------------------------------------------------------------------- destruct H98 as [K H98].
assert (* AndElim *) ((euclidean__axioms.OnCirc K L) /\ (euclidean__axioms.OnCirc K R)) as H99.
------------------------------------------------------------------------------------ exact H98.
------------------------------------------------------------------------------------ destruct H99 as [H99 H100].
assert (* Cut *) (euclidean__axioms.Cong F K F D) as H101.
------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__circle__center__radius (F) (F) (D) (L) (K) (H34) H99).
------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F K A a) as H102.
-------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (K) (F) (D) (A) (a) (H101) H59).
-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G K G H21) as H103.
--------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__circle__center__radius (G) (G) (H21) (R) (K) (H36) H100).
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G K C c) as H104.
---------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (G) (K) (G) (H21) (C) (c) (H103) H24).
---------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H105.
----------------------------------------------------------------------------------------- intro H105.
assert (* Cut *) ((F = G) \/ ((F = K) \/ ((G = K) \/ ((euclidean__axioms.BetS G F K) \/ ((euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G)))))) as H106.
------------------------------------------------------------------------------------------ exact H105.
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol F G K) as H107.
------------------------------------------------------------------------------------------- assert (* Cut *) ((F = G) \/ ((F = K) \/ ((G = K) \/ ((euclidean__axioms.BetS G F K) \/ ((euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G)))))) as H107.
-------------------------------------------------------------------------------------------- exact H106.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((F = G) \/ ((F = K) \/ ((G = K) \/ ((euclidean__axioms.BetS G F K) \/ ((euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G)))))) as __TmpHyp.
--------------------------------------------------------------------------------------------- exact H107.
--------------------------------------------------------------------------------------------- assert (F = G \/ (F = K) \/ ((G = K) \/ ((euclidean__axioms.BetS G F K) \/ ((euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G))))) as H108.
---------------------------------------------------------------------------------------------- exact __TmpHyp.
---------------------------------------------------------------------------------------------- destruct H108 as [H108|H108].
----------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H109.
------------------------------------------------------------------------------------------------ intro H109.
apply (@H18 H108).
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H109).
----------------------------------------------------------------------------------------------- assert (F = K \/ (G = K) \/ ((euclidean__axioms.BetS G F K) \/ ((euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G)))) as H109.
------------------------------------------------------------------------------------------------ exact H108.
------------------------------------------------------------------------------------------------ destruct H109 as [H109|H109].
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A a F K) as H110.
-------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (F) (K) (a) H102).
-------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H111.
--------------------------------------------------------------------------------------------------- intro H111.
assert (* Cut *) (euclidean__axioms.neq F K) as H112.
---------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__nocollapse (A) (a) (F) (K) (H74) H110).
---------------------------------------------------------------------------------------------------- apply (@H112 H109).
--------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H111).
------------------------------------------------------------------------------------------------- assert (G = K \/ (euclidean__axioms.BetS G F K) \/ ((euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G))) as H110.
-------------------------------------------------------------------------------------------------- exact H109.
-------------------------------------------------------------------------------------------------- destruct H110 as [H110|H110].
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C c G K) as H111.
---------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (G) (K) (c) H104).
---------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H112.
----------------------------------------------------------------------------------------------------- intro H112.
assert (* Cut *) (euclidean__axioms.neq G K) as H113.
------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__nocollapse (C) (c) (G) (K) (H76) H111).
------------------------------------------------------------------------------------------------------ apply (@H113 H110).
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H112).
--------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS G F K \/ (euclidean__axioms.BetS F G K) \/ (euclidean__axioms.BetS F K G)) as H111.
---------------------------------------------------------------------------------------------------- exact H110.
---------------------------------------------------------------------------------------------------- destruct H111 as [H111|H111].
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K F G) as H112.
------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (G) (F) (K) H111).
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong K F A a) as H113.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong K F a A) /\ ((euclidean__axioms.Cong K F A a) /\ (euclidean__axioms.Cong F K a A))) as H113.
-------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (K) (A) (a) H102).
-------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong K F a A) /\ ((euclidean__axioms.Cong K F A a) /\ (euclidean__axioms.Cong F K a A))) as H114.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- destruct H114 as [H114 H115].
assert (* AndElim *) ((euclidean__axioms.Cong K F A a) /\ (euclidean__axioms.Cong F K a A)) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
exact H116.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS A a S) /\ ((euclidean__axioms.Cong a S B b) /\ (euclidean__defs.Lt C c A S))) as H114.
-------------------------------------------------------------------------------------------------------- exact H.
-------------------------------------------------------------------------------------------------------- assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS A a S) /\ ((euclidean__axioms.Cong a S B b) /\ (euclidean__defs.Lt C c A S)))) as H115.
--------------------------------------------------------------------------------------------------------- exact H114.
--------------------------------------------------------------------------------------------------------- destruct H115 as [S H115].
assert (* AndElim *) ((euclidean__axioms.BetS A a S) /\ ((euclidean__axioms.Cong a S B b) /\ (euclidean__defs.Lt C c A S))) as H116.
---------------------------------------------------------------------------------------------------------- exact H115.
---------------------------------------------------------------------------------------------------------- destruct H116 as [H116 H117].
assert (* AndElim *) ((euclidean__axioms.Cong a S B b) /\ (euclidean__defs.Lt C c A S)) as H118.
----------------------------------------------------------------------------------------------------------- exact H117.
----------------------------------------------------------------------------------------------------------- destruct H118 as [H118 H119].
assert (* Cut *) (euclidean__axioms.Cong A a K F) as H120.
------------------------------------------------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (K) (F) (a) H113).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong a S F G) as H121.
------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (a) (S) (B) (b) (F) (G) (H118) H17).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A S K G) as H122.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__sumofparts (A) (a) (S) (K) (F) (G) (H120) (H121) (H116) H112).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A S G K) as H123.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong S A G K) /\ ((euclidean__axioms.Cong S A K G) /\ (euclidean__axioms.Cong A S G K))) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (S) (K) (G) H122).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong S A G K) /\ ((euclidean__axioms.Cong S A K G) /\ (euclidean__axioms.Cong A S G K))) as H124.
----------------------------------------------------------------------------------------------------------------- exact H123.
----------------------------------------------------------------------------------------------------------------- destruct H124 as [H124 H125].
assert (* AndElim *) ((euclidean__axioms.Cong S A K G) /\ (euclidean__axioms.Cong A S G K)) as H126.
------------------------------------------------------------------------------------------------------------------ exact H125.
------------------------------------------------------------------------------------------------------------------ destruct H126 as [H126 H127].
exact H127.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt C c G K) as H124.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__lessthancongruence.lemma__lessthancongruence (C) (c) (A) (S) (G) (K) (H119) H123).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C c G K) as H125.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (G) (K) (c) H104).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt G K G K) as H126.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (C) (c) (G) (K) (G) (K) (H124) H125).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H127.
------------------------------------------------------------------------------------------------------------------- intro H127.
assert (* Cut *) (~(euclidean__defs.Lt G K G K)) as H128.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 (G) (K) (G) (K) H126).
-------------------------------------------------------------------------------------------------------------------- apply (@H128 H126).
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H127).
----------------------------------------------------------------------------------------------------- assert (euclidean__axioms.BetS F G K \/ euclidean__axioms.BetS F K G) as H112.
------------------------------------------------------------------------------------------------------ exact H111.
------------------------------------------------------------------------------------------------------ destruct H112 as [H112|H112].
------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS B b S) /\ ((euclidean__axioms.Cong b S C c) /\ (euclidean__defs.Lt A a B S))) as H113.
-------------------------------------------------------------------------------------------------------- exact H1.
-------------------------------------------------------------------------------------------------------- assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS B b S) /\ ((euclidean__axioms.Cong b S C c) /\ (euclidean__defs.Lt A a B S)))) as H114.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- destruct H114 as [S H114].
assert (* AndElim *) ((euclidean__axioms.BetS B b S) /\ ((euclidean__axioms.Cong b S C c) /\ (euclidean__defs.Lt A a B S))) as H115.
---------------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Cong b S C c) /\ (euclidean__defs.Lt A a B S)) as H117.
----------------------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* Cut *) (euclidean__axioms.Cong C c b S) as H119.
------------------------------------------------------------------------------------------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (b) (S) (c) H117).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong G K b S) as H120.
------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (G) (K) (C) (c) (b) (S) (H104) H119).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F K B S) as H121.
-------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__sumofparts (F) (G) (K) (B) (b) (S) (H16) (H120) (H112) H115).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A a F K) as H122.
--------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (F) (K) (a) H102).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F K B S) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (A) (a) (B) (S) (F) (K) (H118) H122).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B S F K) as H124.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (F) (K) (S) H121).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F K F K) as H125.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (F) (K) (B) (S) (F) (K) (H123) H124).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H126.
------------------------------------------------------------------------------------------------------------------- intro H126.
assert (* Cut *) (~(euclidean__defs.Lt F K F K)) as H127.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 (F) (K) (F) (K) H125).
-------------------------------------------------------------------------------------------------------------------- apply (@H127 H125).
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H126).
------------------------------------------------------------------------------------------------------- assert (* Cut *) (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS A a S) /\ ((euclidean__axioms.Cong a S C c) /\ (euclidean__defs.Lt B b A S))) as H113.
-------------------------------------------------------------------------------------------------------- exact H0.
-------------------------------------------------------------------------------------------------------- assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS A a S) /\ ((euclidean__axioms.Cong a S C c) /\ (euclidean__defs.Lt B b A S)))) as H114.
--------------------------------------------------------------------------------------------------------- exact H113.
--------------------------------------------------------------------------------------------------------- destruct H114 as [S H114].
assert (* AndElim *) ((euclidean__axioms.BetS A a S) /\ ((euclidean__axioms.Cong a S C c) /\ (euclidean__defs.Lt B b A S))) as H115.
---------------------------------------------------------------------------------------------------------- exact H114.
---------------------------------------------------------------------------------------------------------- destruct H115 as [H115 H116].
assert (* AndElim *) ((euclidean__axioms.Cong a S C c) /\ (euclidean__defs.Lt B b A S)) as H117.
----------------------------------------------------------------------------------------------------------- exact H116.
----------------------------------------------------------------------------------------------------------- destruct H117 as [H117 H118].
assert (* Cut *) (euclidean__defs.Lt F G A S) as H119.
------------------------------------------------------------------------------------------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (B) (b) (A) (S) (F) (G) (H118) H17).
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong C c a S) as H120.
------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (C) (a) (S) (c) H117).
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong G K a S) as H121.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (G) (K) (C) (c) (a) (S) (H104) H120).
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong K G a S) as H122.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong K G S a) /\ ((euclidean__axioms.Cong K G a S) /\ (euclidean__axioms.Cong G K S a))) as H122.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (G) (K) (a) (S) H121).
---------------------------------------------------------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong K G S a) /\ ((euclidean__axioms.Cong K G a S) /\ (euclidean__axioms.Cong G K S a))) as H123.
----------------------------------------------------------------------------------------------------------------- exact H122.
----------------------------------------------------------------------------------------------------------------- destruct H123 as [H123 H124].
assert (* AndElim *) ((euclidean__axioms.Cong K G a S) /\ (euclidean__axioms.Cong G K S a)) as H125.
------------------------------------------------------------------------------------------------------------------ exact H124.
------------------------------------------------------------------------------------------------------------------ destruct H125 as [H125 H126].
exact H125.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong F G A S) as H123.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.cn__sumofparts (F) (K) (G) (A) (a) (S) (H102) (H122) (H112) H115).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong A S F G) as H124.
----------------------------------------------------------------------------------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (F) (G) (S) H123).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Lt F G F G) as H125.
------------------------------------------------------------------------------------------------------------------ apply (@lemma__lessthancongruence.lemma__lessthancongruence (F) (G) (A) (S) (F) (G) (H119) H124).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (~(euclidean__axioms.Col F G K)) as H126.
------------------------------------------------------------------------------------------------------------------- intro H126.
assert (* Cut *) (~(euclidean__defs.Lt F G F G)) as H127.
-------------------------------------------------------------------------------------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 (F) (G) (F) (G) H125).
-------------------------------------------------------------------------------------------------------------------- apply (@H127 H125).
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H126).
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (F) (G) (K) (H107) H106).
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Triangle F G K) as H106.
------------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol (F) (G) (K) H105).
------------------------------------------------------------------------------------------ exists G.
exists K.
split.
------------------------------------------------------------------------------------------- exact H16.
------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------- exact H102.
-------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------- exact H104.
--------------------------------------------------------------------------------------------- split.
---------------------------------------------------------------------------------------------- exact H15.
---------------------------------------------------------------------------------------------- exact H106.
Qed.
