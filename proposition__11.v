Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__doublereverse.
Require Export lemma__extension.
Require Export logic.
Require Export proposition__01.
Definition proposition__11 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.BetS A C B) -> (exists (X: euclidean__axioms.Point), euclidean__defs.Per A C X).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (euclidean__axioms.neq A C) as H0.
- assert (* Cut *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H0.
-- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (C) (B) H).
-- assert (* AndElim *) ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B))) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A B)) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
exact H3.
- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E A C)) as H1.
-- apply (@lemma__extension.lemma__extension (A) (C) (A) (C) (H0) H0).
-- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E A C))) as H2.
--- exact H1.
--- destruct H2 as [E H2].
assert (* AndElim *) ((euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E A C)) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* Cut *) (euclidean__axioms.neq A E) as H5.
----- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A E))) as H5.
------ apply (@lemma__betweennotequal.lemma__betweennotequal (A) (C) (E) H3).
------ assert (* AndElim *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A E))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A E)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
exact H9.
----- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__defs.equilateral A E F) /\ (euclidean__axioms.Triangle A E F)) as H6.
------ apply (@proposition__01.proposition__01 (A) (E) H5).
------ assert (exists F: euclidean__axioms.Point, ((euclidean__defs.equilateral A E F) /\ (euclidean__axioms.Triangle A E F))) as H7.
------- exact H6.
------- destruct H7 as [F H7].
assert (* AndElim *) ((euclidean__defs.equilateral A E F) /\ (euclidean__axioms.Triangle A E F)) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* Cut *) (euclidean__axioms.Cong E F F A) as H10.
--------- assert (* AndElim *) ((euclidean__axioms.Cong A E E F) /\ (euclidean__axioms.Cong E F F A)) as H10.
---------- exact H8.
---------- destruct H10 as [H10 H11].
exact H11.
--------- assert (* Cut *) (euclidean__axioms.Cong A F F E) as H11.
---------- assert (* Cut *) ((euclidean__axioms.Cong A F F E) /\ (euclidean__axioms.Cong F E A F)) as H11.
----------- apply (@lemma__doublereverse.lemma__doublereverse (E) (F) (F) (A) H10).
----------- assert (* AndElim *) ((euclidean__axioms.Cong A F F E) /\ (euclidean__axioms.Cong F E A F)) as H12.
------------ exact H11.
------------ destruct H12 as [H12 H13].
exact H12.
---------- assert (* Cut *) (euclidean__axioms.Cong A F E F) as H12.
----------- assert (* Cut *) ((euclidean__axioms.Cong F A E F) /\ ((euclidean__axioms.Cong F A F E) /\ (euclidean__axioms.Cong A F E F))) as H12.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip (A) (F) (F) (E) H11).
------------ assert (* AndElim *) ((euclidean__axioms.Cong F A E F) /\ ((euclidean__axioms.Cong F A F E) /\ (euclidean__axioms.Cong A F E F))) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Cong F A F E) /\ (euclidean__axioms.Cong A F E F)) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
exact H16.
----------- assert (* Cut *) (~(C = F)) as H13.
------------ intro H13.
assert (* Cut *) (euclidean__axioms.Col A C E) as H14.
------------- right.
right.
right.
right.
left.
exact H3.
------------- assert (* Cut *) (euclidean__axioms.Col A F E) as H15.
-------------- apply (@eq__ind__r euclidean__axioms.Point F (fun C0: euclidean__axioms.Point => (euclidean__axioms.BetS A C0 B) -> ((euclidean__axioms.neq A C0) -> ((euclidean__axioms.BetS A C0 E) -> ((euclidean__axioms.Cong C0 E A C0) -> ((euclidean__axioms.Col A C0 E) -> (euclidean__axioms.Col A F E))))))) with (x := C).
---------------intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
exact H19.

--------------- exact H13.
--------------- exact H.
--------------- exact H0.
--------------- exact H3.
--------------- exact H4.
--------------- exact H14.
-------------- assert (* Cut *) (euclidean__axioms.Col A E F) as H16.
--------------- assert (* Cut *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))))) as H16.
---------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (F) (E) H15).
---------------- assert (* AndElim *) ((euclidean__axioms.Col F A E) /\ ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))))) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col F E A) /\ ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A)))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col E A F) /\ ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col A E F) /\ (euclidean__axioms.Col E F A)) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
exact H23.
--------------- assert (* Cut *) (euclidean__axioms.nCol A E F) as H17.
---------------- exact H9.
---------------- apply (@euclidean__tactics.Col__nCol__False (A) (E) (F) (H17) H16).
------------ assert (* Cut *) (euclidean__axioms.Cong C A E C) as H14.
------------- assert (* Cut *) ((euclidean__axioms.Cong C A E C) /\ (euclidean__axioms.Cong E C C A)) as H14.
-------------- apply (@lemma__doublereverse.lemma__doublereverse (C) (E) (A) (C) H4).
-------------- assert (* AndElim *) ((euclidean__axioms.Cong C A E C) /\ (euclidean__axioms.Cong E C C A)) as H15.
--------------- exact H14.
--------------- destruct H15 as [H15 H16].
exact H15.
------------- assert (* Cut *) (euclidean__axioms.Cong A C E C) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.Cong A C C E) /\ ((euclidean__axioms.Cong A C E C) /\ (euclidean__axioms.Cong C A C E))) as H15.
--------------- apply (@lemma__congruenceflip.lemma__congruenceflip (C) (A) (E) (C) H14).
--------------- assert (* AndElim *) ((euclidean__axioms.Cong A C C E) /\ ((euclidean__axioms.Cong A C E C) /\ (euclidean__axioms.Cong C A C E))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong A C E C) /\ (euclidean__axioms.Cong C A C E)) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
exact H18.
-------------- assert (* Cut *) (euclidean__defs.Per A C F) as H16.
--------------- exists E.
split.
---------------- exact H3.
---------------- split.
----------------- exact H15.
----------------- split.
------------------ exact H12.
------------------ exact H13.
--------------- exists F.
exact H16.
Qed.
