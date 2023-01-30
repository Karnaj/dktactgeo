Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6a.
Require Export lemma__3__7a.
Require Export lemma__3__7b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray1.
Require Export lemma__ray3.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__supplements : forall A B C D F a b c d f, (euclidean__defs.CongA A B C a b c) -> ((euclidean__defs.Supp A B C D F) -> ((euclidean__defs.Supp a b c d f) -> (euclidean__defs.CongA D B F d b f))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro F.
intro a.
intro b.
intro c.
intro d.
intro f.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.BetS A B F) as H2.
- destruct H1 as [H2 H3].
destruct H0 as [H4 H5].
exact H5.
- assert (* Cut *) (euclidean__defs.Out B C D) as H3.
-- destruct H1 as [H3 H4].
destruct H0 as [H5 H6].
exact H5.
-- assert (* Cut *) (euclidean__axioms.BetS a b f) as H4.
--- destruct H1 as [H4 H5].
destruct H0 as [H6 H7].
exact H5.
--- assert (* Cut *) (euclidean__defs.Out b c d) as H5.
---- destruct H1 as [H5 H6].
destruct H0 as [H7 H8].
exact H5.
---- assert (exists U V u v, (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H6 by exact H.
destruct H6 as [U H7].
destruct H7 as [V H8].
destruct H8 as [u H9].
destruct H9 as [v H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
assert (* Cut *) (euclidean__axioms.neq A B) as H25.
----- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H25.
------ apply (@lemma__betweennotequal.lemma__betweennotequal A B F H2).
------ destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H28.
----- assert (* Cut *) (euclidean__axioms.neq B U) as H26.
------ apply (@lemma__raystrict.lemma__raystrict B A U H11).
------ assert (* Cut *) (euclidean__axioms.neq U B) as H27.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B U H26).
------- assert (* Cut *) (euclidean__axioms.neq b u) as H28.
-------- apply (@lemma__raystrict.lemma__raystrict b a u H15).
-------- assert (* Cut *) (euclidean__axioms.neq u b) as H29.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric b u H28).
--------- assert (* Cut *) (exists W, (euclidean__axioms.BetS U B W) /\ (euclidean__axioms.Cong B W U B)) as H30.
---------- apply (@lemma__extension.lemma__extension U B U B H27 H27).
---------- destruct H30 as [W H31].
destruct H31 as [H32 H33].
assert (* Cut *) (euclidean__axioms.neq a b) as H34.
----------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a f))) as H34.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal a b f H4).
------------ destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
----------- assert (* Cut *) (exists w, (euclidean__axioms.BetS u b w) /\ (euclidean__axioms.Cong b w U B)) as H35.
------------ apply (@lemma__extension.lemma__extension u b U B H29 H27).
------------ destruct H35 as [w H36].
destruct H36 as [H37 H38].
assert (* Cut *) (euclidean__axioms.Cong U B b w) as H39.
------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric U b w B H38).
------------- assert (* Cut *) (euclidean__axioms.Cong B W b w) as H40.
-------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive B W U B b w H33 H39).
-------------- assert (* Cut *) (euclidean__axioms.Cong U B u b) as H41.
--------------- assert (* Cut *) ((euclidean__axioms.Cong U B u b) /\ ((euclidean__axioms.Cong U B b u) /\ (euclidean__axioms.Cong B U u b))) as H41.
---------------- apply (@lemma__congruenceflip.lemma__congruenceflip B U b u H19).
---------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H42.
--------------- assert (* Cut *) (euclidean__axioms.Cong V W v w) as H42.
---------------- apply (@euclidean__axioms.axiom__5__line U B W V u b w v H40 H23 H21 H32 H37 H41).
---------------- assert (* Cut *) ((euclidean__axioms.BetS B U A) \/ ((A = U) \/ (euclidean__axioms.BetS B A U))) as H43.
----------------- apply (@lemma__ray1.lemma__ray1 B A U H11).
----------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H44.
------------------ assert ((euclidean__axioms.BetS B U A) \/ ((A = U) \/ (euclidean__axioms.BetS B A U))) as H44 by exact H43.
assert ((euclidean__axioms.BetS B U A) \/ ((A = U) \/ (euclidean__axioms.BetS B A U))) as __TmpHyp by exact H44.
destruct __TmpHyp as [H45|H45].
------------------- assert (* Cut *) (euclidean__axioms.BetS A U B) as H46.
-------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B U A H45).
-------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H47.
--------------------- apply (@lemma__3__7a.lemma__3__7a A U B W H46 H32).
--------------------- exact H47.
------------------- destruct H45 as [H46|H46].
-------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H47.
--------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun A0 => (euclidean__defs.CongA A0 B C a b c) -> ((euclidean__defs.Supp A0 B C D F) -> ((euclidean__axioms.BetS A0 B F) -> ((euclidean__defs.Out B A0 U) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.neq A0 B) -> (euclidean__axioms.BetS A0 B W)))))))) with (x := A).
----------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
exact H32.

---------------------- exact H46.
---------------------- exact H.
---------------------- exact H0.
---------------------- exact H2.
---------------------- exact H11.
---------------------- exact H24.
---------------------- exact H25.
--------------------- exact H47.
-------------------- assert (* Cut *) (euclidean__axioms.BetS U A B) as H47.
--------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry B A U H46).
--------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H48.
---------------------- apply (@lemma__3__6a.lemma__3__6a U A B W H47 H32).
---------------------- exact H48.
------------------ assert (* Cut *) (euclidean__defs.Out B F W) as H45.
------------------- exists A.
split.
-------------------- exact H44.
-------------------- exact H2.
------------------- assert (* Cut *) ((euclidean__axioms.BetS B W F) \/ ((F = W) \/ (euclidean__axioms.BetS B F W))) as H46.
-------------------- apply (@lemma__ray1.lemma__ray1 B F W H45).
-------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H47.
--------------------- assert ((euclidean__axioms.BetS B W F) \/ ((F = W) \/ (euclidean__axioms.BetS B F W))) as H47 by exact H46.
assert ((euclidean__axioms.BetS B W F) \/ ((F = W) \/ (euclidean__axioms.BetS B F W))) as __TmpHyp by exact H47.
destruct __TmpHyp as [H48|H48].
---------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H49.
----------------------- apply (@lemma__3__7b.lemma__3__7b U B W F H32 H48).
----------------------- exact H49.
---------------------- destruct H48 as [H49|H49].
----------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H50.
------------------------ apply (@eq__ind__r euclidean__axioms.Point W (fun F0 => (euclidean__defs.Supp A B C D F0) -> ((euclidean__axioms.BetS A B F0) -> ((euclidean__defs.Out B F0 W) -> (euclidean__axioms.BetS U B F0))))) with (x := F).
-------------------------intro H50.
intro H51.
intro H52.
exact H32.

------------------------- exact H49.
------------------------- exact H0.
------------------------- exact H2.
------------------------- exact H45.
------------------------ exact H50.
----------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H50.
------------------------ apply (@euclidean__axioms.axiom__innertransitivity U B F W H32 H49).
------------------------ exact H50.
--------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H48.
---------------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq U B) /\ (euclidean__axioms.neq U F))) as H48.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal U B F H47).
----------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
---------------------- assert (* Cut *) (euclidean__defs.Out B F W) as H49.
----------------------- exists A.
split.
------------------------ exact H44.
------------------------ exact H2.
----------------------- assert (* Cut *) ((euclidean__axioms.BetS b u a) \/ ((a = u) \/ (euclidean__axioms.BetS b a u))) as H50.
------------------------ apply (@lemma__ray1.lemma__ray1 b a u H15).
------------------------ assert (* Cut *) (euclidean__axioms.BetS a b w) as H51.
------------------------- assert ((euclidean__axioms.BetS b u a) \/ ((a = u) \/ (euclidean__axioms.BetS b a u))) as H51 by exact H50.
assert ((euclidean__axioms.BetS b u a) \/ ((a = u) \/ (euclidean__axioms.BetS b a u))) as __TmpHyp by exact H51.
destruct __TmpHyp as [H52|H52].
-------------------------- assert (* Cut *) (euclidean__axioms.BetS a u b) as H53.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry b u a H52).
--------------------------- assert (* Cut *) (euclidean__axioms.BetS a b w) as H54.
---------------------------- apply (@lemma__3__7a.lemma__3__7a a u b w H53 H37).
---------------------------- exact H54.
-------------------------- destruct H52 as [H53|H53].
--------------------------- assert (* Cut *) (euclidean__axioms.BetS a b w) as H54.
---------------------------- apply (@eq__ind__r euclidean__axioms.Point u (fun a0 => (euclidean__defs.CongA A B C a0 b c) -> ((euclidean__defs.Supp a0 b c d f) -> ((euclidean__axioms.BetS a0 b f) -> ((euclidean__defs.Out b a0 u) -> ((euclidean__axioms.neq a0 b) -> (euclidean__axioms.BetS a0 b w))))))) with (x := a).
-----------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
exact H37.

----------------------------- exact H53.
----------------------------- exact H.
----------------------------- exact H1.
----------------------------- exact H4.
----------------------------- exact H15.
----------------------------- exact H34.
---------------------------- exact H54.
--------------------------- assert (* Cut *) (euclidean__axioms.BetS u a b) as H54.
---------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry b a u H53).
---------------------------- assert (* Cut *) (euclidean__axioms.BetS a b w) as H55.
----------------------------- apply (@lemma__3__6a.lemma__3__6a u a b w H54 H37).
----------------------------- exact H55.
------------------------- assert (* Cut *) (euclidean__defs.Out b f w) as H52.
-------------------------- exists a.
split.
--------------------------- exact H51.
--------------------------- exact H4.
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS b w f) \/ ((f = w) \/ (euclidean__axioms.BetS b f w))) as H53.
--------------------------- apply (@lemma__ray1.lemma__ray1 b f w H52).
--------------------------- assert (* Cut *) (euclidean__axioms.BetS u b f) as H54.
---------------------------- assert ((euclidean__axioms.BetS b w f) \/ ((f = w) \/ (euclidean__axioms.BetS b f w))) as H54 by exact H53.
assert ((euclidean__axioms.BetS b w f) \/ ((f = w) \/ (euclidean__axioms.BetS b f w))) as __TmpHyp by exact H54.
destruct __TmpHyp as [H55|H55].
----------------------------- assert (* Cut *) (euclidean__axioms.BetS u b f) as H56.
------------------------------ apply (@lemma__3__7b.lemma__3__7b u b w f H37 H55).
------------------------------ exact H56.
----------------------------- destruct H55 as [H56|H56].
------------------------------ assert (* Cut *) (euclidean__axioms.BetS u b f) as H57.
------------------------------- apply (@eq__ind__r euclidean__axioms.Point w (fun f0 => (euclidean__defs.Supp a b c d f0) -> ((euclidean__axioms.BetS a b f0) -> ((euclidean__defs.Out b f0 w) -> (euclidean__axioms.BetS u b f0))))) with (x := f).
--------------------------------intro H57.
intro H58.
intro H59.
exact H37.

-------------------------------- exact H56.
-------------------------------- exact H1.
-------------------------------- exact H4.
-------------------------------- exact H52.
------------------------------- exact H57.
------------------------------ assert (* Cut *) (euclidean__axioms.BetS u b f) as H57.
------------------------------- apply (@euclidean__axioms.axiom__innertransitivity u b f w H37 H56).
------------------------------- exact H57.
---------------------------- assert (* Cut *) (euclidean__axioms.neq b f) as H55.
----------------------------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H55.
------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal u b f H54).
------------------------------ destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H56.
----------------------------- assert (* Cut *) (euclidean__defs.Out b f w) as H56.
------------------------------ exists a.
split.
------------------------------- exact H51.
------------------------------- exact H4.
------------------------------ assert (* Cut *) (euclidean__axioms.neq b f) as H57.
------------------------------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H57.
-------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal u b f H54).
-------------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H55.
------------------------------- assert (* Cut *) (euclidean__defs.Out b f w) as H58.
-------------------------------- exists a.
split.
--------------------------------- exact H51.
--------------------------------- exact H4.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col U B W) as H59.
--------------------------------- right.
right.
right.
right.
left.
exact H32.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B A U) as H60.
---------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B A U H11).
---------------------------------- assert (* Cut *) (~(euclidean__axioms.Col D B F)) as H61.
----------------------------------- intro H61.
assert (* Cut *) (euclidean__axioms.Col B C D) as H62.
------------------------------------ apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear B C D H3).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col D B C) as H63.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H63.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C D H62).
-------------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H68.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H64.
-------------------------------------- apply (@lemma__raystrict.lemma__raystrict B C D H3).
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq D B) as H65.
--------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B D H64).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Col B F C) as H66.
---------------------------------------- apply (@euclidean__tactics.not__nCol__Col B F C).
-----------------------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False B F C H66).
------------------------------------------apply (@lemma__collinear4.lemma__collinear4 D B F C H61 H63 H65).


---------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H67.
----------------------------------------- right.
right.
right.
right.
left.
exact H2.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B A) as H68.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H68.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B F H67).
------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H76.
------------------------------------------ assert (* Cut *) (euclidean__axioms.Col F B C) as H69.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col B C F) /\ (euclidean__axioms.Col C F B))))) as H69.
-------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B F C H66).
-------------------------------------------- destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
exact H70.
------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H70.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H70.
--------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal u b f H54).
--------------------------------------------- destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H48.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq F B) as H71.
--------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B F H70).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H72.
---------------------------------------------- apply (@euclidean__tactics.not__nCol__Col B A C).
-----------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False B A C H72).
------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 F B A C H68 H69 H71).


---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H73.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H73.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder B A C H72).
------------------------------------------------ destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
exact H74.
----------------------------------------------- apply (@euclidean__tactics.Col__nCol__False A B C H24 H73).
----------------------------------- assert (* Cut *) (euclidean__defs.Out B D V) as H62.
------------------------------------ apply (@lemma__ray3.lemma__ray3 B C D V H3 H13).
------------------------------------ assert (* Cut *) (euclidean__defs.Out b d v) as H63.
------------------------------------- apply (@lemma__ray3.lemma__ray3 b c d v H5 H17).
------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B F d b f) as H64.
-------------------------------------- exists V.
exists W.
exists v.
exists w.
split.
--------------------------------------- exact H62.
--------------------------------------- split.
---------------------------------------- exact H49.
---------------------------------------- split.
----------------------------------------- exact H63.
----------------------------------------- split.
------------------------------------------ exact H58.
------------------------------------------ split.
------------------------------------------- exact H21.
------------------------------------------- split.
-------------------------------------------- exact H40.
-------------------------------------------- split.
--------------------------------------------- exact H42.
--------------------------------------------- apply (@euclidean__tactics.nCol__notCol D B F H61).
-------------------------------------- exact H64.
Qed.
