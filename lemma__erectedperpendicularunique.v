Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__10__12.
Require Export lemma__8__3.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__layoff.
Require Export lemma__ray5.
Require Export lemma__rightangleNC.
Require Export lemma__sameside2.
Require Export logic.
Require Export proposition__07.
Definition lemma__erectedperpendicularunique : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__defs.Per A B C) -> ((euclidean__defs.Per A B E) -> ((euclidean__defs.OS C E A B) -> (euclidean__defs.Out B C E))).
Proof.
intro A.
intro B.
intro C.
intro E.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (D: euclidean__axioms.Point), (euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H2.
- exact H.
- assert (exists D: euclidean__axioms.Point, ((euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C))))) as H3.
-- exact H2.
-- destruct H3 as [D H3].
assert (* AndElim *) ((euclidean__axioms.BetS A B D) /\ ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)))) as H4.
--- exact H3.
--- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Cong A B D B) /\ ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C))) as H6.
---- exact H5.
---- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Cong A C D C) /\ (euclidean__axioms.neq B C)) as H8.
----- exact H7.
----- destruct H8 as [H8 H9].
assert (* Cut *) (euclidean__axioms.neq B E) as H10.
------ assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A E X E) /\ (euclidean__axioms.neq B E)))) as H10.
------- exact H0.
------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A E X E) /\ (euclidean__axioms.neq B E)))) as __TmpHyp.
-------- exact H10.
-------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A E X E) /\ (euclidean__axioms.neq B E))))) as H11.
--------- exact __TmpHyp.
--------- destruct H11 as [x H11].
assert (* AndElim *) ((euclidean__axioms.BetS A B x) /\ ((euclidean__axioms.Cong A B x B) /\ ((euclidean__axioms.Cong A E x E) /\ (euclidean__axioms.neq B E)))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Cong A B x B) /\ ((euclidean__axioms.Cong A E x E) /\ (euclidean__axioms.neq B E))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Cong A E x E) /\ (euclidean__axioms.neq B E)) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C)))) as H18.
------------- exact H.
------------- assert (* Cut *) (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C)))) as __TmpHyp0.
-------------- exact H18.
-------------- assert (exists X: euclidean__axioms.Point, ((euclidean__axioms.BetS A B X) /\ ((euclidean__axioms.Cong A B X B) /\ ((euclidean__axioms.Cong A C X C) /\ (euclidean__axioms.neq B C))))) as H19.
--------------- exact __TmpHyp0.
--------------- destruct H19 as [x0 H19].
assert (* AndElim *) ((euclidean__axioms.BetS A B x0) /\ ((euclidean__axioms.Cong A B x0 B) /\ ((euclidean__axioms.Cong A C x0 C) /\ (euclidean__axioms.neq B C)))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Cong A B x0 B) /\ ((euclidean__axioms.Cong A C x0 C) /\ (euclidean__axioms.neq B C))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Cong A C x0 C) /\ (euclidean__axioms.neq B C)) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
exact H17.
------ assert (* Cut *) (exists (H11: euclidean__axioms.Point), (euclidean__defs.Out B E H11) /\ (euclidean__axioms.Cong B H11 B C)) as H11.
------- apply (@lemma__layoff.lemma__layoff (B) (E) (B) (C) (H10) H9).
------- assert (exists H12: euclidean__axioms.Point, ((euclidean__defs.Out B E H12) /\ (euclidean__axioms.Cong B H12 B C))) as H13.
-------- exact H11.
-------- destruct H13 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Out B E H12) /\ (euclidean__axioms.Cong B H12 B C)) as H14.
--------- exact H13.
--------- destruct H14 as [H14 H15].
assert (* Cut *) (B = B) as H16.
---------- apply (@logic.eq__refl (Point) B).
---------- assert (* Cut *) (euclidean__axioms.Col A B B) as H17.
----------- right.
right.
left.
exact H16.
----------- assert (* Cut *) (euclidean__defs.OS C H12 A B) as H18.
------------ apply (@lemma__sameside2.lemma__sameside2 (A) (B) (B) (C) (E) (H12) (H1) (H17) H14).
------------ assert (* Cut *) (euclidean__defs.Per A B H12) as H19.
------------- apply (@lemma__8__3.lemma__8__3 (A) (B) (E) (H12) (H0) H14).
------------- assert (* Cut *) (euclidean__axioms.Cong B C B H12) as H20.
-------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (H12) (C) H15).
-------------- assert (* Cut *) (euclidean__axioms.Cong A C A H12) as H21.
--------------- apply (@lemma__10__12.lemma__10__12 (A) (B) (C) (H12) (H) (H19) H20).
--------------- assert (* Cut *) (euclidean__axioms.Cong C A H12 A) as H22.
---------------- assert (* Cut *) ((euclidean__axioms.Cong C A H12 A) /\ ((euclidean__axioms.Cong C A A H12) /\ (euclidean__axioms.Cong A C H12 A))) as H22.
----------------- apply (@lemma__congruenceflip.lemma__congruenceflip (A) (C) (A) (H12) H21).
----------------- assert (* AndElim *) ((euclidean__axioms.Cong C A H12 A) /\ ((euclidean__axioms.Cong C A A H12) /\ (euclidean__axioms.Cong A C H12 A))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Cong C A A H12) /\ (euclidean__axioms.Cong A C H12 A)) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
exact H23.
---------------- assert (* Cut *) (euclidean__axioms.Cong C B H12 B) as H23.
----------------- assert (* Cut *) ((euclidean__axioms.Cong C B H12 B) /\ ((euclidean__axioms.Cong C B B H12) /\ (euclidean__axioms.Cong B C H12 B))) as H23.
------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (B) (C) (B) (H12) H20).
------------------ assert (* AndElim *) ((euclidean__axioms.Cong C B H12 B) /\ ((euclidean__axioms.Cong C B B H12) /\ (euclidean__axioms.Cong B C H12 B))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.Cong C B B H12) /\ (euclidean__axioms.Cong B C H12 B)) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
exact H24.
----------------- assert (* Cut *) (~(A = B)) as H24.
------------------ intro H24.
assert (* Cut *) (euclidean__axioms.Col A B C) as H25.
------------------- left.
exact H24.
------------------- assert (* Cut *) (euclidean__axioms.nCol A B C) as H26.
-------------------- apply (@lemma__rightangleNC.lemma__rightangleNC (A) (B) (C) H).
-------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H26) H25).
------------------ assert (* Cut *) (C = H12) as H25.
------------------- apply (@proposition__07.proposition__07 (A) (B) (C) (H12) (H24) (H22) (H23) H18).
------------------- assert (* Cut *) (euclidean__defs.Out B E C) as H26.
-------------------- apply (@eq__ind__r euclidean__axioms.Point H12 (fun C0: euclidean__axioms.Point => (euclidean__defs.Per A B C0) -> ((euclidean__defs.OS C0 E A B) -> ((euclidean__axioms.Cong A C0 D C0) -> ((euclidean__axioms.neq B C0) -> ((euclidean__axioms.Cong B H12 B C0) -> ((euclidean__defs.OS C0 H12 A B) -> ((euclidean__axioms.Cong B C0 B H12) -> ((euclidean__axioms.Cong A C0 A H12) -> ((euclidean__axioms.Cong C0 A H12 A) -> ((euclidean__axioms.Cong C0 B H12 B) -> (euclidean__defs.Out B E C0)))))))))))) with (x := C).
---------------------intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
exact H14.

--------------------- exact H25.
--------------------- exact H.
--------------------- exact H1.
--------------------- exact H8.
--------------------- exact H9.
--------------------- exact H15.
--------------------- exact H18.
--------------------- exact H20.
--------------------- exact H21.
--------------------- exact H22.
--------------------- exact H23.
-------------------- assert (* Cut *) (euclidean__defs.Out B C E) as H27.
--------------------- apply (@lemma__ray5.lemma__ray5 (B) (E) (C) H26).
--------------------- exact H27.
Qed.
