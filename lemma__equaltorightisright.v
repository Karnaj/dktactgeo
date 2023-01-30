Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalanglessymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray5.
Require Export lemma__raystrict.
Require Export logic.
Definition lemma__equaltorightisright : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.Per A B C) -> ((euclidean__defs.CongA a b c A B C) -> (euclidean__defs.Per a b c)).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.CongA A B C a b c) as H1.
- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (a) (b) (c) (A) (B) (C) H0).
- assert (* Cut *) (exists (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (e: euclidean__axioms.Point) (f: euclidean__axioms.Point), (euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C)))))))) as H2.
-- exact H1.
-- assert (exists E: euclidean__axioms.Point, (exists (F: euclidean__axioms.Point) (e: euclidean__axioms.Point) (f: euclidean__axioms.Point), (euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))))))))) as H3.
--- exact H2.
--- destruct H3 as [E H3].
assert (exists F: euclidean__axioms.Point, (exists (e: euclidean__axioms.Point) (f: euclidean__axioms.Point), (euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))))))))) as H4.
---- exact H3.
---- destruct H4 as [F H4].
assert (exists e: euclidean__axioms.Point, (exists (f: euclidean__axioms.Point), (euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))))))))) as H5.
----- exact H4.
----- destruct H5 as [e H5].
assert (exists f: euclidean__axioms.Point, ((euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))))))))) as H6.
------ exact H5.
------ destruct H6 as [f H6].
assert (* AndElim *) ((euclidean__defs.Out B A E) /\ ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C)))))))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out B C F) /\ ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.Out b a e) /\ ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C)))))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.Out b c f) /\ ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong B E b e) /\ ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C)))) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Cong B F b f) /\ ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C))) as H17.
------------ exact H16.
------------ destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Cong E F e f) /\ (euclidean__axioms.nCol A B C)) as H19.
------------- exact H18.
------------- destruct H19 as [H19 H20].
assert (* Cut *) (euclidean__defs.Per A B F) as H21.
-------------- apply (@lemma__8__3.lemma__8__3 (A) (B) (C) (F) (H) H9).
-------------- assert (* Cut *) (euclidean__defs.Per F B A) as H22.
--------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (F) H21).
--------------- assert (* Cut *) (euclidean__defs.Per F B E) as H23.
---------------- apply (@lemma__8__3.lemma__8__3 (F) (B) (A) (E) (H22) H7).
---------------- assert (* Cut *) (euclidean__defs.Per E B F) as H24.
----------------- apply (@lemma__8__2.lemma__8__2 (F) (B) (E) H23).
----------------- assert (* Cut *) (euclidean__axioms.neq B E) as H25.
------------------ apply (@lemma__raystrict.lemma__raystrict (B) (A) (E) H7).
------------------ assert (* Cut *) (euclidean__axioms.neq E B) as H26.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (E) H25).
------------------- assert (* Cut *) (exists (W: euclidean__axioms.Point), (euclidean__axioms.BetS E B W) /\ ((euclidean__axioms.Cong E B W B) /\ ((euclidean__axioms.Cong E F W F) /\ (euclidean__axioms.neq B F)))) as H27.
-------------------- exact H24.
-------------------- assert (exists W: euclidean__axioms.Point, ((euclidean__axioms.BetS E B W) /\ ((euclidean__axioms.Cong E B W B) /\ ((euclidean__axioms.Cong E F W F) /\ (euclidean__axioms.neq B F))))) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [W H28].
assert (* AndElim *) ((euclidean__axioms.BetS E B W) /\ ((euclidean__axioms.Cong E B W B) /\ ((euclidean__axioms.Cong E F W F) /\ (euclidean__axioms.neq B F)))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Cong E B W B) /\ ((euclidean__axioms.Cong E F W F) /\ (euclidean__axioms.neq B F))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Cong E F W F) /\ (euclidean__axioms.neq B F)) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
assert (* Cut *) (euclidean__axioms.neq b e) as H35.
------------------------- apply (@euclidean__axioms.axiom__nocollapse (B) (E) (b) (e) (H25) H15).
------------------------- assert (* Cut *) (euclidean__axioms.neq e b) as H36.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (b) (e) H35).
-------------------------- assert (* Cut *) (exists (w: euclidean__axioms.Point), (euclidean__axioms.BetS e b w) /\ (euclidean__axioms.Cong b w e b)) as H37.
--------------------------- apply (@lemma__extension.lemma__extension (e) (b) (e) (b) (H36) H36).
--------------------------- assert (exists w: euclidean__axioms.Point, ((euclidean__axioms.BetS e b w) /\ (euclidean__axioms.Cong b w e b))) as H38.
---------------------------- exact H37.
---------------------------- destruct H38 as [w H38].
assert (* AndElim *) ((euclidean__axioms.BetS e b w) /\ (euclidean__axioms.Cong b w e b)) as H39.
----------------------------- exact H38.
----------------------------- destruct H39 as [H39 H40].
assert (* Cut *) (euclidean__axioms.Cong e b E B) as H41.
------------------------------ assert (* Cut *) ((euclidean__axioms.Cong e b E B) /\ (euclidean__axioms.Cong E B e b)) as H41.
------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (B) (E) (b) (e) H15).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong e b E B) /\ (euclidean__axioms.Cong E B e b)) as H42.
-------------------------------- exact H41.
-------------------------------- destruct H42 as [H42 H43].
exact H42.
------------------------------ assert (* Cut *) (euclidean__axioms.Cong b w E B) as H42.
------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (b) (w) (e) (b) (E) (B) (H40) H41).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong E B B W) as H43.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Cong B E B W) /\ ((euclidean__axioms.Cong B E W B) /\ (euclidean__axioms.Cong E B B W))) as H43.
--------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (E) (B) (W) (B) H31).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong B E B W) /\ ((euclidean__axioms.Cong B E W B) /\ (euclidean__axioms.Cong E B B W))) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Cong B E W B) /\ (euclidean__axioms.Cong E B B W)) as H46.
----------------------------------- exact H45.
----------------------------------- destruct H46 as [H46 H47].
exact H47.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong b w B W) as H44.
--------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (b) (w) (E) (B) (B) (W) (H42) H43).
--------------------------------- assert (* Cut *) (euclidean__axioms.Cong b f B F) as H45.
---------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (b) (B) (F) (f) H17).
---------------------------------- assert (* Cut *) (euclidean__axioms.Cong e f E F) as H46.
----------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (e) (E) (F) (f) H19).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong e w E W) as H47.
------------------------------------ apply (@euclidean__axioms.cn__sumofparts (e) (b) (w) (E) (B) (W) (H41) (H44) (H39) H29).
------------------------------------ assert (* Cut *) (euclidean__axioms.Cong f w F W) as H48.
------------------------------------- apply (@euclidean__axioms.axiom__5__line (e) (b) (w) (f) (E) (B) (W) (F) (H44) (H46) (H45) (H39) (H29) H41).
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e b B W) as H49.
-------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (e) (b) (E) (B) (B) (W) (H41) H43).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Cong B W b w) as H50.
--------------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (b) (w) (W) H44).
--------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e b b w) as H51.
---------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (e) (b) (B) (W) (b) (w) (H49) H50).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e b w b) as H52.
----------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong b e w b) /\ ((euclidean__axioms.Cong b e b w) /\ (euclidean__axioms.Cong e b w b))) as H52.
------------------------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (e) (b) (b) (w) H51).
------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Cong b e w b) /\ ((euclidean__axioms.Cong b e b w) /\ (euclidean__axioms.Cong e b w b))) as H53.
------------------------------------------- exact H52.
------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Cong b e b w) /\ (euclidean__axioms.Cong e b w b)) as H55.
-------------------------------------------- exact H54.
-------------------------------------------- destruct H55 as [H55 H56].
exact H56.
----------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e f W F) as H53.
------------------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (e) (f) (E) (F) (W) (F) (H46) H33).
------------------------------------------ assert (* Cut *) (euclidean__axioms.Cong W F w f) as H54.
------------------------------------------- assert (* Cut *) ((euclidean__axioms.Cong W F w f) /\ (euclidean__axioms.Cong w f W F)) as H54.
-------------------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (f) (w) (F) (W) H48).
-------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong W F w f) /\ (euclidean__axioms.Cong w f W F)) as H55.
--------------------------------------------- exact H54.
--------------------------------------------- destruct H55 as [H55 H56].
exact H55.
------------------------------------------- assert (* Cut *) (euclidean__axioms.Cong e f w f) as H55.
-------------------------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (e) (f) (W) (F) (w) (f) (H53) H54).
-------------------------------------------- assert (* Cut *) (euclidean__axioms.neq b f) as H56.
--------------------------------------------- apply (@lemma__raystrict.lemma__raystrict (b) (c) (f) H13).
--------------------------------------------- assert (* Cut *) (euclidean__defs.Per e b f) as H57.
---------------------------------------------- exists w.
split.
----------------------------------------------- exact H39.
----------------------------------------------- split.
------------------------------------------------ exact H52.
------------------------------------------------ split.
------------------------------------------------- exact H55.
------------------------------------------------- exact H56.
---------------------------------------------- assert (* Cut *) (euclidean__defs.Out b f c) as H58.
----------------------------------------------- apply (@lemma__ray5.lemma__ray5 (b) (c) (f) H13).
----------------------------------------------- assert (* Cut *) (euclidean__defs.Per e b c) as H59.
------------------------------------------------ apply (@lemma__8__3.lemma__8__3 (e) (b) (f) (c) (H57) H58).
------------------------------------------------ assert (* Cut *) (euclidean__defs.Per c b e) as H60.
------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (e) (b) (c) H59).
------------------------------------------------- assert (* Cut *) (euclidean__defs.Out b e a) as H61.
-------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (b) (a) (e) H11).
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Per c b a) as H62.
--------------------------------------------------- apply (@lemma__8__3.lemma__8__3 (c) (b) (e) (a) (H60) H61).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Per a b c) as H63.
---------------------------------------------------- apply (@lemma__8__2.lemma__8__2 (c) (b) (a) H62).
---------------------------------------------------- exact H63.
Qed.
