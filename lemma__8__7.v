Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__8__3.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__droppedperpendicularunique.
Require Export lemma__extension.
Require Export lemma__extensionunique.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Definition lemma__8__7 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__defs.Per C B A) -> (~(euclidean__defs.Per A C B)).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__axioms.neq B A) as H0.
- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C B X) /\ ((euclidean__axioms.Cong C B X B) /\ ((euclidean__axioms.Cong C A X A) /\ (euclidean__axioms.neq B A)))) as H0.
-- exact H.
-- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C B X) /\ ((euclidean__axioms.Cong C B X B) /\ ((euclidean__axioms.Cong C A X A) /\ (euclidean__axioms.neq B A)))) as __TmpHyp.
--- exact H0.
--- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C B X) /\ ((euclidean__axioms.Cong C B X B) /\ ((euclidean__axioms.Cong C A X A) /\ (euclidean__axioms.neq B A))))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [x H1].
assert (* AndElim *) ((euclidean__axioms.BetS C B x) /\ ((euclidean__axioms.Cong C B x B) /\ ((euclidean__axioms.Cong C A x A) /\ (euclidean__axioms.neq B A)))) as H2.
----- exact H1.
----- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__axioms.Cong C B x B) /\ ((euclidean__axioms.Cong C A x A) /\ (euclidean__axioms.neq B A))) as H4.
------ exact H3.
------ destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Cong C A x A) /\ (euclidean__axioms.neq B A)) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
exact H7.
- assert (* Cut *) (euclidean__defs.Per A B C) as H1.
-- apply (@lemma__8__2.lemma__8__2 (C) (B) (A) H).
-- assert (* Cut *) (euclidean__axioms.neq B C) as H2.
--- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C)))) as H2.
---- exact H1.
---- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C)))) as __TmpHyp.
----- exact H2.
----- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C))))) as H3.
------ exact __TmpHyp.
------ destruct H3 as [x H3].
assert (* AndElim *) ((euclidean__axioms.BetS A B x) /\ ((euclidean__axioms.Cong A B x B) /\ ((euclidean__axioms.Cong A C x C) /\ (euclidean__axioms.neq B C)))) as H4.
------- exact H3.
------- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Cong A B x B) /\ ((euclidean__axioms.Cong A C x C) /\ (euclidean__axioms.neq B C))) as H6.
-------- exact H5.
-------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Cong A C x C) /\ (euclidean__axioms.neq B C)) as H8.
--------- exact H7.
--------- destruct H8 as [H8 H9].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C B X) /\ ((euclidean__axioms.Cong C B X B) /\ ((euclidean__axioms.Cong C A X A) /\ (euclidean__axioms.neq B A)))) as H10.
---------- exact H.
---------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS C B X) /\ ((euclidean__axioms.Cong C B X B) /\ ((euclidean__axioms.Cong C A X A) /\ (euclidean__axioms.neq B A)))) as __TmpHyp0.
----------- exact H10.
----------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS C B X) /\ ((euclidean__axioms.Cong C B X B) /\ ((euclidean__axioms.Cong C A X A) /\ (euclidean__axioms.neq B A))))) as H11.
------------ exact __TmpHyp0.
------------ destruct H11 as [x0 H11].
assert (* AndElim *) ((euclidean__axioms.BetS C B x0) /\ ((euclidean__axioms.Cong C B x0 B) /\ ((euclidean__axioms.Cong C A x0 A) /\ (euclidean__axioms.neq B A)))) as H12.
------------- exact H11.
------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Cong C B x0 B) /\ ((euclidean__axioms.Cong C A x0 A) /\ (euclidean__axioms.neq B A))) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong C A x0 A) /\ (euclidean__axioms.neq B A)) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
exact H9.
--- assert (* Cut *) (euclidean__axioms.neq C B) as H3.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (C) H2).
---- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS B C E) /\ (euclidean__axioms.Cong C E C B)) as H4.
----- apply (@lemma__extension.lemma__extension (B) (C) (C) (B) (H2) H3).
----- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS B C E) /\ (euclidean__axioms.Cong C E C B))) as H5.
------ exact H4.
------ destruct H5 as [E H5].
assert (* AndElim *) ((euclidean__axioms.BetS B C E) /\ (euclidean__axioms.Cong C E C B)) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* Cut *) (euclidean__axioms.Col B C E) as H8.
-------- right.
right.
right.
right.
left.
exact H6.
-------- assert (* Cut *) (euclidean__axioms.Col E C B) as H9.
--------- assert (* Cut *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H9.
---------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (E) H8).
---------- assert (* AndElim *) ((euclidean__axioms.Col C B E) /\ ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))))) as H10.
----------- exact H9.
----------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col C E B) /\ ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)))) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col E B C) /\ ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col B E C) /\ (euclidean__axioms.Col E C B)) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
exact H17.
--------- assert (* Cut *) (euclidean__defs.Per A B C) as H10.
---------- exact H1.
---------- assert (* Cut *) (euclidean__defs.Out B C E) as H11.
----------- apply (@lemma__ray4.lemma__ray4 (B) (C) (E)).
------------right.
right.
exact H6.

------------ exact H2.
----------- assert (* Cut *) (euclidean__defs.Per A B E) as H12.
------------ apply (@lemma__8__3.lemma__8__3 (A) (B) (C) (E) (H10) H11).
------------ assert (* Cut *) (euclidean__defs.Per E B A) as H13.
------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (E) H12).
------------- assert (* Cut *) (~(euclidean__defs.Per A C B)) as H14.
-------------- intro H14.
assert (* Cut *) (euclidean__defs.Per B C A) as H15.
--------------- apply (@lemma__8__2.lemma__8__2 (A) (C) (B) H14).
--------------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS B C F) /\ ((euclidean__axioms.Cong B C F C) /\ ((euclidean__axioms.Cong B A F A) /\ (euclidean__axioms.neq C A)))) as H16.
---------------- exact H15.
---------------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS B C F) /\ ((euclidean__axioms.Cong B C F C) /\ ((euclidean__axioms.Cong B A F A) /\ (euclidean__axioms.neq C A))))) as H17.
----------------- exact H16.
----------------- destruct H17 as [F H17].
assert (* AndElim *) ((euclidean__axioms.BetS B C F) /\ ((euclidean__axioms.Cong B C F C) /\ ((euclidean__axioms.Cong B A F A) /\ (euclidean__axioms.neq C A)))) as H18.
------------------ exact H17.
------------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Cong B C F C) /\ ((euclidean__axioms.Cong B A F A) /\ (euclidean__axioms.neq C A))) as H20.
------------------- exact H19.
------------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong B A F A) /\ (euclidean__axioms.neq C A)) as H22.
-------------------- exact H21.
-------------------- destruct H22 as [H22 H23].
assert (* Cut *) (euclidean__axioms.Cong F C B C) as H24.
--------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (B) (C) (C) H20).
--------------------- assert (* Cut *) (euclidean__axioms.Cong C F B C) as H25.
---------------------- assert (* Cut *) ((euclidean__axioms.Cong C F C B) /\ ((euclidean__axioms.Cong C F B C) /\ (euclidean__axioms.Cong F C C B))) as H25.
----------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (F) (C) (B) (C) H24).
----------------------- assert (* AndElim *) ((euclidean__axioms.Cong C F C B) /\ ((euclidean__axioms.Cong C F B C) /\ (euclidean__axioms.Cong F C C B))) as H26.
------------------------ exact H25.
------------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.Cong C F B C) /\ (euclidean__axioms.Cong F C C B)) as H28.
------------------------- exact H27.
------------------------- destruct H28 as [H28 H29].
exact H28.
---------------------- assert (* Cut *) (euclidean__axioms.Cong C E B C) as H26.
----------------------- assert (* Cut *) ((euclidean__axioms.Cong E C B C) /\ ((euclidean__axioms.Cong E C C B) /\ (euclidean__axioms.Cong C E B C))) as H26.
------------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (C) (E) (C) (B) H7).
------------------------ assert (* AndElim *) ((euclidean__axioms.Cong E C B C) /\ ((euclidean__axioms.Cong E C C B) /\ (euclidean__axioms.Cong C E B C))) as H27.
------------------------- exact H26.
------------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Cong E C C B) /\ (euclidean__axioms.Cong C E B C)) as H29.
-------------------------- exact H28.
-------------------------- destruct H29 as [H29 H30].
exact H30.
----------------------- assert (* Cut *) (euclidean__axioms.Cong B C C E) as H27.
------------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (C) (E) (C) H26).
------------------------ assert (* Cut *) (euclidean__axioms.Cong C F C E) as H28.
------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (F) (B) (C) (C) (E) (H25) H27).
------------------------- assert (* Cut *) (F = E) as H29.
-------------------------- apply (@lemma__extensionunique.lemma__extensionunique (B) (C) (F) (E) (H18) (H6) H28).
-------------------------- assert (* Cut *) (euclidean__axioms.BetS E C B) as H30.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (C) (E) H6).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong F A B A) as H31.
---------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (F) (B) (A) (A) H22).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong E A B A) as H32.
----------------------------- apply (@eq__ind__r euclidean__axioms.Point E (fun F0: euclidean__axioms.Point => (euclidean__axioms.BetS B C F0) -> ((euclidean__axioms.Cong B C F0 C) -> ((euclidean__axioms.Cong B A F0 A) -> ((euclidean__axioms.Cong F0 C B C) -> ((euclidean__axioms.Cong C F0 B C) -> ((euclidean__axioms.Cong C F0 C E) -> ((euclidean__axioms.Cong F0 A B A) -> (euclidean__axioms.Cong E A B A))))))))) with (x := F).
------------------------------intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
exact H38.

------------------------------ exact H29.
------------------------------ exact H18.
------------------------------ exact H20.
------------------------------ exact H22.
------------------------------ exact H24.
------------------------------ exact H25.
------------------------------ exact H28.
------------------------------ exact H31.
----------------------------- assert (* Cut *) (euclidean__axioms.Cong E C B C) as H33.
------------------------------ assert (* Cut *) ((euclidean__axioms.Cong E C C B) /\ ((euclidean__axioms.Cong E C B C) /\ (euclidean__axioms.Cong C E C B))) as H33.
------------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (E) (B) (C) H26).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong E C C B) /\ ((euclidean__axioms.Cong E C B C) /\ (euclidean__axioms.Cong C E C B))) as H34.
-------------------------------- exact H33.
-------------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Cong E C B C) /\ (euclidean__axioms.Cong C E C B)) as H36.
--------------------------------- exact H35.
--------------------------------- destruct H36 as [H36 H37].
exact H36.
------------------------------ assert (* Cut *) (euclidean__defs.Per E C A) as H34.
------------------------------- exists B.
split.
-------------------------------- exact H30.
-------------------------------- split.
--------------------------------- exact H33.
--------------------------------- split.
---------------------------------- exact H32.
---------------------------------- exact H23.
------------------------------- assert (* Cut *) (C = B) as H35.
-------------------------------- apply (@lemma__droppedperpendicularunique.lemma__droppedperpendicularunique (E) (B) (C) (A) (H34) (H13) H9).
-------------------------------- apply (@H3 H35).
-------------- exact H14.
Qed.
