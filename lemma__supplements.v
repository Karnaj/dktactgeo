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
Definition lemma__supplements : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (F: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (f: euclidean__axioms.Point), (euclidean__defs.CongA A B C a b c) -> ((euclidean__defs.Supp A B C D F) -> ((euclidean__defs.Supp a b c d f) -> (euclidean__defs.CongA D B F d b f))).
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
- assert (* AndElim *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as H2.
-- exact H1.
-- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H4.
--- exact H0.
--- destruct H4 as [H4 H5].
exact H5.
- assert (* Cut *) (euclidean__defs.Out B C D) as H3.
-- assert (* AndElim *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as H3.
--- exact H1.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H5.
---- exact H0.
---- destruct H5 as [H5 H6].
exact H5.
-- assert (* Cut *) (euclidean__axioms.BetS a b f) as H4.
--- assert (* AndElim *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as H4.
---- exact H1.
---- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H6.
----- exact H0.
----- destruct H6 as [H6 H7].
exact H5.
--- assert (* Cut *) (euclidean__defs.Out b c d) as H5.
---- assert (* AndElim *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as H5.
----- exact H1.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H7.
------ exact H0.
------ destruct H7 as [H7 H8].
exact H5.
---- assert (* Cut *) (exists (U: euclidean__axioms.Point) (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H6.
----- exact H.
----- assert (exists U: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point) (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H7.
------ exact H6.
------ destruct H7 as [U H7].
assert (exists V: euclidean__axioms.Point, (exists (u: euclidean__axioms.Point) (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H8.
------- exact H7.
------- destruct H8 as [V H8].
assert (exists u: euclidean__axioms.Point, (exists (v: euclidean__axioms.Point), (euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H9.
-------- exact H8.
-------- destruct H9 as [u H9].
assert (exists v: euclidean__axioms.Point, ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))))) as H10.
--------- exact H9.
--------- destruct H10 as [v H10].
assert (* AndElim *) ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Out B C V) /\ ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.Out b a u) /\ ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.Out b c v) /\ ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong B U b u) /\ ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)))) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Cong B V b v) /\ ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C))) as H21.
--------------- exact H20.
--------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Cong U V u v) /\ (euclidean__axioms.nCol A B C)) as H23.
---------------- exact H22.
---------------- destruct H23 as [H23 H24].
assert (* Cut *) (euclidean__axioms.neq A B) as H25.
----------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H25.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (F) H2).
------------------ assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F)) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
exact H28.
----------------- assert (* Cut *) (euclidean__axioms.neq B U) as H26.
------------------ apply (@lemma__raystrict.lemma__raystrict (B) (A) (U) H11).
------------------ assert (* Cut *) (euclidean__axioms.neq U B) as H27.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (U) H26).
------------------- assert (* Cut *) (euclidean__axioms.neq b u) as H28.
-------------------- apply (@lemma__raystrict.lemma__raystrict (b) (a) (u) H15).
-------------------- assert (* Cut *) (euclidean__axioms.neq u b) as H29.
--------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (b) (u) H28).
--------------------- assert (* Cut *) (exists (W: euclidean__axioms.Point), (euclidean__axioms.BetS U B W) /\ (euclidean__axioms.Cong B W U B)) as H30.
---------------------- apply (@lemma__extension.lemma__extension (U) (B) (U) (B) (H27) H27).
---------------------- assert (exists W: euclidean__axioms.Point, ((euclidean__axioms.BetS U B W) /\ (euclidean__axioms.Cong B W U B))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [W H31].
assert (* AndElim *) ((euclidean__axioms.BetS U B W) /\ (euclidean__axioms.Cong B W U B)) as H32.
------------------------ exact H31.
------------------------ destruct H32 as [H32 H33].
assert (* Cut *) (euclidean__axioms.neq a b) as H34.
------------------------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a f))) as H34.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (a) (b) (f) H4).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a f))) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ (euclidean__axioms.neq a f)) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
exact H37.
------------------------- assert (* Cut *) (exists (w: euclidean__axioms.Point), (euclidean__axioms.BetS u b w) /\ (euclidean__axioms.Cong b w U B)) as H35.
-------------------------- apply (@lemma__extension.lemma__extension (u) (b) (U) (B) (H29) H27).
-------------------------- assert (exists w: euclidean__axioms.Point, ((euclidean__axioms.BetS u b w) /\ (euclidean__axioms.Cong b w U B))) as H36.
--------------------------- exact H35.
--------------------------- destruct H36 as [w H36].
assert (* AndElim *) ((euclidean__axioms.BetS u b w) /\ (euclidean__axioms.Cong b w U B)) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
assert (* Cut *) (euclidean__axioms.Cong U B b w) as H39.
----------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (U) (b) (w) (B) H38).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong B W b w) as H40.
------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (W) (U) (B) (b) (w) (H33) H39).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong U B u b) as H41.
------------------------------- assert (* Cut *) ((euclidean__axioms.Cong U B u b) /\ ((euclidean__axioms.Cong U B b u) /\ (euclidean__axioms.Cong B U u b))) as H41.
-------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (B) (U) (b) (u) H19).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong U B u b) /\ ((euclidean__axioms.Cong U B b u) /\ (euclidean__axioms.Cong B U u b))) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Cong U B b u) /\ (euclidean__axioms.Cong B U u b)) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
exact H42.
------------------------------- assert (* Cut *) (euclidean__axioms.Cong V W v w) as H42.
-------------------------------- apply (@euclidean__axioms.axiom__5__line (U) (B) (W) (V) (u) (b) (w) (v) (H40) (H23) (H21) (H32) (H37) H41).
-------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B U A) \/ ((A = U) \/ (euclidean__axioms.BetS B A U))) as H43.
--------------------------------- apply (@lemma__ray1.lemma__ray1 (B) (A) (U) H11).
--------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H44.
---------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B U A) \/ ((A = U) \/ (euclidean__axioms.BetS B A U))) as H44.
----------------------------------- exact H43.
----------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B U A) \/ ((A = U) \/ (euclidean__axioms.BetS B A U))) as __TmpHyp.
------------------------------------ exact H44.
------------------------------------ assert (euclidean__axioms.BetS B U A \/ (A = U) \/ (euclidean__axioms.BetS B A U)) as H45.
------------------------------------- exact __TmpHyp.
------------------------------------- destruct H45 as [H45|H45].
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A U B) as H46.
--------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (U) (A) H45).
--------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H47.
---------------------------------------- apply (@lemma__3__7a.lemma__3__7a (A) (U) (B) (W) (H46) H32).
---------------------------------------- exact H47.
-------------------------------------- assert (A = U \/ euclidean__axioms.BetS B A U) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46|H46].
---------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H47.
----------------------------------------- apply (@eq__ind__r euclidean__axioms.Point U (fun A0: euclidean__axioms.Point => (euclidean__defs.CongA A0 B C a b c) -> ((euclidean__defs.Supp A0 B C D F) -> ((euclidean__axioms.BetS A0 B F) -> ((euclidean__defs.Out B A0 U) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.neq A0 B) -> (euclidean__axioms.BetS A0 B W)))))))) with (x := A).
------------------------------------------intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
exact H32.

------------------------------------------ exact H46.
------------------------------------------ exact H.
------------------------------------------ exact H0.
------------------------------------------ exact H2.
------------------------------------------ exact H11.
------------------------------------------ exact H24.
------------------------------------------ exact H25.
----------------------------------------- exact H47.
---------------------------------------- assert (* Cut *) (euclidean__axioms.BetS U A B) as H47.
----------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (A) (U) H46).
----------------------------------------- assert (* Cut *) (euclidean__axioms.BetS A B W) as H48.
------------------------------------------ apply (@lemma__3__6a.lemma__3__6a (U) (A) (B) (W) (H47) H32).
------------------------------------------ exact H48.
---------------------------------- assert (* Cut *) (euclidean__defs.Out B F W) as H45.
----------------------------------- exists A.
split.
------------------------------------ exact H44.
------------------------------------ exact H2.
----------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B W F) \/ ((F = W) \/ (euclidean__axioms.BetS B F W))) as H46.
------------------------------------ apply (@lemma__ray1.lemma__ray1 (B) (F) (W) H45).
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS U B F) as H47.
------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B W F) \/ ((F = W) \/ (euclidean__axioms.BetS B F W))) as H47.
-------------------------------------- exact H46.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS B W F) \/ ((F = W) \/ (euclidean__axioms.BetS B F W))) as __TmpHyp.
--------------------------------------- exact H47.
--------------------------------------- assert (euclidean__axioms.BetS B W F \/ (F = W) \/ (euclidean__axioms.BetS B F W)) as H48.
---------------------------------------- exact __TmpHyp.
---------------------------------------- destruct H48 as [H48|H48].
----------------------------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H49.
------------------------------------------ apply (@lemma__3__7b.lemma__3__7b (U) (B) (W) (F) (H32) H48).
------------------------------------------ exact H49.
----------------------------------------- assert (F = W \/ euclidean__axioms.BetS B F W) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49|H49].
------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H50.
-------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point W (fun F0: euclidean__axioms.Point => (euclidean__defs.Supp A B C D F0) -> ((euclidean__axioms.BetS A B F0) -> ((euclidean__defs.Out B F0 W) -> (euclidean__axioms.BetS U B F0))))) with (x := F).
---------------------------------------------intro H50.
intro H51.
intro H52.
exact H32.

--------------------------------------------- exact H49.
--------------------------------------------- exact H0.
--------------------------------------------- exact H2.
--------------------------------------------- exact H45.
-------------------------------------------- exact H50.
------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS U B F) as H50.
-------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (U) (B) (F) (W) (H32) H49).
-------------------------------------------- exact H50.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H48.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq U B) /\ (euclidean__axioms.neq U F))) as H48.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (U) (B) (F) H47).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq U B) /\ (euclidean__axioms.neq U F))) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq U B) /\ (euclidean__axioms.neq U F)) as H51.
----------------------------------------- exact H50.
----------------------------------------- destruct H51 as [H51 H52].
exact H49.
-------------------------------------- assert (* Cut *) (euclidean__defs.Out B F W) as H49.
--------------------------------------- exists A.
split.
---------------------------------------- exact H44.
---------------------------------------- exact H2.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS b u a) \/ ((a = u) \/ (euclidean__axioms.BetS b a u))) as H50.
---------------------------------------- apply (@lemma__ray1.lemma__ray1 (b) (a) (u) H15).
---------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a b w) as H51.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS b u a) \/ ((a = u) \/ (euclidean__axioms.BetS b a u))) as H51.
------------------------------------------ exact H50.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS b u a) \/ ((a = u) \/ (euclidean__axioms.BetS b a u))) as __TmpHyp.
------------------------------------------- exact H51.
------------------------------------------- assert (euclidean__axioms.BetS b u a \/ (a = u) \/ (euclidean__axioms.BetS b a u)) as H52.
-------------------------------------------- exact __TmpHyp.
-------------------------------------------- destruct H52 as [H52|H52].
--------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a u b) as H53.
---------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (b) (u) (a) H52).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a b w) as H54.
----------------------------------------------- apply (@lemma__3__7a.lemma__3__7a (a) (u) (b) (w) (H53) H37).
----------------------------------------------- exact H54.
--------------------------------------------- assert (a = u \/ euclidean__axioms.BetS b a u) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53|H53].
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS a b w) as H54.
------------------------------------------------ apply (@eq__ind__r euclidean__axioms.Point u (fun a0: euclidean__axioms.Point => (euclidean__defs.CongA A B C a0 b c) -> ((euclidean__defs.Supp a0 b c d f) -> ((euclidean__axioms.BetS a0 b f) -> ((euclidean__defs.Out b a0 u) -> ((euclidean__axioms.neq a0 b) -> (euclidean__axioms.BetS a0 b w))))))) with (x := a).
-------------------------------------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
exact H37.

------------------------------------------------- exact H53.
------------------------------------------------- exact H.
------------------------------------------------- exact H1.
------------------------------------------------- exact H4.
------------------------------------------------- exact H15.
------------------------------------------------- exact H34.
------------------------------------------------ exact H54.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS u a b) as H54.
------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (b) (a) (u) H53).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS a b w) as H55.
------------------------------------------------- apply (@lemma__3__6a.lemma__3__6a (u) (a) (b) (w) (H54) H37).
------------------------------------------------- exact H55.
----------------------------------------- assert (* Cut *) (euclidean__defs.Out b f w) as H52.
------------------------------------------ exists a.
split.
------------------------------------------- exact H51.
------------------------------------------- exact H4.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.BetS b w f) \/ ((f = w) \/ (euclidean__axioms.BetS b f w))) as H53.
------------------------------------------- apply (@lemma__ray1.lemma__ray1 (b) (f) (w) H52).
------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS u b f) as H54.
-------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS b w f) \/ ((f = w) \/ (euclidean__axioms.BetS b f w))) as H54.
--------------------------------------------- exact H53.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.BetS b w f) \/ ((f = w) \/ (euclidean__axioms.BetS b f w))) as __TmpHyp.
---------------------------------------------- exact H54.
---------------------------------------------- assert (euclidean__axioms.BetS b w f \/ (f = w) \/ (euclidean__axioms.BetS b f w)) as H55.
----------------------------------------------- exact __TmpHyp.
----------------------------------------------- destruct H55 as [H55|H55].
------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS u b f) as H56.
------------------------------------------------- apply (@lemma__3__7b.lemma__3__7b (u) (b) (w) (f) (H37) H55).
------------------------------------------------- exact H56.
------------------------------------------------ assert (f = w \/ euclidean__axioms.BetS b f w) as H56.
------------------------------------------------- exact H55.
------------------------------------------------- destruct H56 as [H56|H56].
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS u b f) as H57.
--------------------------------------------------- apply (@eq__ind__r euclidean__axioms.Point w (fun f0: euclidean__axioms.Point => (euclidean__defs.Supp a b c d f0) -> ((euclidean__axioms.BetS a b f0) -> ((euclidean__defs.Out b f0 w) -> (euclidean__axioms.BetS u b f0))))) with (x := f).
----------------------------------------------------intro H57.
intro H58.
intro H59.
exact H37.

---------------------------------------------------- exact H56.
---------------------------------------------------- exact H1.
---------------------------------------------------- exact H4.
---------------------------------------------------- exact H52.
--------------------------------------------------- exact H57.
-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS u b f) as H57.
--------------------------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (u) (b) (f) (w) (H37) H56).
--------------------------------------------------- exact H57.
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq b f) as H55.
--------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H55.
---------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (u) (b) (f) H54).
---------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H56.
----------------------------------------------- exact H55.
----------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f)) as H58.
------------------------------------------------ exact H57.
------------------------------------------------ destruct H58 as [H58 H59].
exact H56.
--------------------------------------------- assert (* Cut *) (euclidean__defs.Out b f w) as H56.
---------------------------------------------- exists a.
split.
----------------------------------------------- exact H51.
----------------------------------------------- exact H4.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.neq b f) as H57.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H57.
------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal (u) (b) (f) H54).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H58.
------------------------------------------------- exact H57.
------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f)) as H60.
-------------------------------------------------- exact H59.
-------------------------------------------------- destruct H60 as [H60 H61].
exact H55.
----------------------------------------------- assert (* Cut *) (euclidean__defs.Out b f w) as H58.
------------------------------------------------ exists a.
split.
------------------------------------------------- exact H51.
------------------------------------------------- exact H4.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col U B W) as H59.
------------------------------------------------- right.
right.
right.
right.
left.
exact H32.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A U) as H60.
-------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (A) (U) H11).
-------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col D B F)) as H61.
--------------------------------------------------- intro H61.
assert (* Cut *) (euclidean__axioms.Col B C D) as H62.
---------------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (C) (D) H3).
---------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B C) as H63.
----------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H63.
------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (D) H62).
------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H64.
------------------------------------------------------- exact H63.
------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)))) as H66.
-------------------------------------------------------- exact H65.
-------------------------------------------------------- destruct H66 as [H66 H67].
assert (* AndElim *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))) as H68.
--------------------------------------------------------- exact H67.
--------------------------------------------------------- destruct H68 as [H68 H69].
assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B)) as H70.
---------------------------------------------------------- exact H69.
---------------------------------------------------------- destruct H70 as [H70 H71].
exact H68.
----------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H64.
------------------------------------------------------ apply (@lemma__raystrict.lemma__raystrict (B) (C) (D) H3).
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D B) as H65.
------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H64).
------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B F C) as H66.
-------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (C)).
---------------------------------------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (C) (H66)).
----------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (F) (C) (H61) (H63) H65).


-------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H67.
--------------------------------------------------------- right.
right.
right.
right.
left.
exact H2.
--------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B A) as H68.
---------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H68.
----------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (F) H67).
----------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H69.
------------------------------------------------------------ exact H68.
------------------------------------------------------------ destruct H69 as [H69 H70].
assert (* AndElim *) ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)))) as H71.
------------------------------------------------------------- exact H70.
------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))) as H73.
-------------------------------------------------------------- exact H72.
-------------------------------------------------------------- destruct H73 as [H73 H74].
assert (* AndElim *) ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A)) as H75.
--------------------------------------------------------------- exact H74.
--------------------------------------------------------------- destruct H75 as [H75 H76].
exact H76.
---------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B C) as H69.
----------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col B C F) /\ (euclidean__axioms.Col C F B))))) as H69.
------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (C) H66).
------------------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col F B C) /\ ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col B C F) /\ (euclidean__axioms.Col C F B))))) as H70.
------------------------------------------------------------- exact H69.
------------------------------------------------------------- destruct H70 as [H70 H71].
assert (* AndElim *) ((euclidean__axioms.Col F C B) /\ ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col B C F) /\ (euclidean__axioms.Col C F B)))) as H72.
-------------------------------------------------------------- exact H71.
-------------------------------------------------------------- destruct H72 as [H72 H73].
assert (* AndElim *) ((euclidean__axioms.Col C B F) /\ ((euclidean__axioms.Col B C F) /\ (euclidean__axioms.Col C F B))) as H74.
--------------------------------------------------------------- exact H73.
--------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col B C F) /\ (euclidean__axioms.Col C F B)) as H76.
---------------------------------------------------------------- exact H75.
---------------------------------------------------------------- destruct H76 as [H76 H77].
exact H70.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B F) as H70.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H70.
------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (u) (b) (f) H54).
------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq b f) /\ ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f))) as H71.
-------------------------------------------------------------- exact H70.
-------------------------------------------------------------- destruct H71 as [H71 H72].
assert (* AndElim *) ((euclidean__axioms.neq u b) /\ (euclidean__axioms.neq u f)) as H73.
--------------------------------------------------------------- exact H72.
--------------------------------------------------------------- destruct H73 as [H73 H74].
exact H48.
------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq F B) as H71.
------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (F) H70).
------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A C) as H72.
-------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (A) (C)).
---------------------------------------------------------------intro H72.
apply (@euclidean__tactics.Col__nCol__False (B) (A) (C) (H72)).
----------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (B) (A) (C) (H68) (H69) H71).


-------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H73.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H73.
---------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (C) H72).
---------------------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H74.
----------------------------------------------------------------- exact H73.
----------------------------------------------------------------- destruct H74 as [H74 H75].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)))) as H76.
------------------------------------------------------------------ exact H75.
------------------------------------------------------------------ destruct H76 as [H76 H77].
assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))) as H78.
------------------------------------------------------------------- exact H77.
------------------------------------------------------------------- destruct H78 as [H78 H79].
assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B)) as H80.
-------------------------------------------------------------------- exact H79.
-------------------------------------------------------------------- destruct H80 as [H80 H81].
exact H74.
--------------------------------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H24) H73).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B D V) as H62.
---------------------------------------------------- apply (@lemma__ray3.lemma__ray3 (B) (C) (D) (V) (H3) H13).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out b d v) as H63.
----------------------------------------------------- apply (@lemma__ray3.lemma__ray3 (b) (c) (d) (v) (H5) H17).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B F d b f) as H64.
------------------------------------------------------ exists V.
exists W.
exists v.
exists w.
split.
------------------------------------------------------- exact H62.
------------------------------------------------------- split.
-------------------------------------------------------- exact H49.
-------------------------------------------------------- split.
--------------------------------------------------------- exact H63.
--------------------------------------------------------- split.
---------------------------------------------------------- exact H58.
---------------------------------------------------------- split.
----------------------------------------------------------- exact H21.
----------------------------------------------------------- split.
------------------------------------------------------------ exact H40.
------------------------------------------------------------ split.
------------------------------------------------------------- exact H42.
------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (D) (B) (F) H61).
------------------------------------------------------ exact H64.
Qed.
