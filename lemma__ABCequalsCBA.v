Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray4.
Require Export logic.
Definition lemma__ABCequalsCBA : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point), (euclidean__axioms.nCol A B C) -> (euclidean__defs.CongA A B C C B A).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(B = A)) as H0.
- intro H0.
assert (* Cut *) (A = B) as H1.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (A) (B) H0).
-- assert (* Cut *) (euclidean__axioms.Col A B C) as H2.
--- left.
exact H1.
--- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H2).
- assert (* Cut *) (~(C = B)) as H1.
-- intro H1.
assert (* Cut *) (euclidean__axioms.Col C B A) as H2.
--- left.
exact H1.
--- assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H3.
----- apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H2).
----- assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H4.
------ exact H3.
------ destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
exact H11.
---- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H3).
-- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS B A E) /\ (euclidean__axioms.Cong A E C B)) as H2.
--- apply (@lemma__extension.lemma__extension (B) (A) (C) (B) (H0) H1).
--- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS B A E) /\ (euclidean__axioms.Cong A E C B))) as H3.
---- exact H2.
---- destruct H3 as [E H3].
assert (* AndElim *) ((euclidean__axioms.BetS B A E) /\ (euclidean__axioms.Cong A E C B)) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* Cut *) (~(B = C)) as H6.
------ intro H6.
assert (* Cut *) (euclidean__axioms.Col A B C) as H7.
------- right.
right.
left.
exact H6.
------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H) H7).
------ assert (* Cut *) (euclidean__axioms.neq A B) as H7.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (A) H0).
------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS B C F) /\ (euclidean__axioms.Cong C F A B)) as H8.
-------- apply (@lemma__extension.lemma__extension (B) (C) (A) (B) (H6) H7).
-------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS B C F) /\ (euclidean__axioms.Cong C F A B))) as H9.
--------- exact H8.
--------- destruct H9 as [F H9].
assert (* AndElim *) ((euclidean__axioms.BetS B C F) /\ (euclidean__axioms.Cong C F A B)) as H10.
---------- exact H9.
---------- destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__axioms.Cong B A F C) as H12.
----------- assert (* Cut *) ((euclidean__axioms.Cong B A F C) /\ (euclidean__axioms.Cong F C B A)) as H12.
------------ apply (@lemma__doublereverse.lemma__doublereverse (C) (F) (A) (B) H11).
------------ assert (* AndElim *) ((euclidean__axioms.Cong B A F C) /\ (euclidean__axioms.Cong F C B A)) as H13.
------------- exact H12.
------------- destruct H13 as [H13 H14].
exact H13.
----------- assert (* Cut *) (euclidean__axioms.BetS F C B) as H13.
------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (C) (F) H10).
------------ assert (* Cut *) (euclidean__axioms.Cong B E F B) as H14.
------------- apply (@euclidean__axioms.cn__sumofparts (B) (A) (E) (F) (C) (B) (H12) (H5) (H4) H13).
------------- assert (* Cut *) (euclidean__axioms.Cong F B B F) as H15.
-------------- apply (@euclidean__axioms.cn__equalityreverse (F) B).
-------------- assert (* Cut *) (euclidean__axioms.Cong B E B F) as H16.
--------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (E) (F) (B) (B) (F) (H14) H15).
--------------- assert (* Cut *) (euclidean__axioms.Cong B F B E) as H17.
---------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (B) (E) (F) H16).
---------------- assert (* Cut *) (euclidean__axioms.Cong E F F E) as H18.
----------------- apply (@euclidean__axioms.cn__equalityreverse (E) F).
----------------- assert (* Cut *) (euclidean__defs.Out B A E) as H19.
------------------ apply (@lemma__ray4.lemma__ray4 (B) (A) (E)).
-------------------right.
right.
exact H4.

------------------- exact H0.
------------------ assert (* Cut *) (euclidean__defs.Out B C F) as H20.
------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (F)).
--------------------right.
right.
exact H10.

-------------------- exact H6.
------------------- assert (* Cut *) (euclidean__defs.CongA A B C C B A) as H21.
-------------------- exists E.
exists F.
exists F.
exists E.
split.
--------------------- exact H19.
--------------------- split.
---------------------- exact H20.
---------------------- split.
----------------------- exact H20.
----------------------- split.
------------------------ exact H19.
------------------------ split.
------------------------- exact H16.
------------------------- split.
-------------------------- exact H17.
-------------------------- split.
--------------------------- exact H18.
--------------------------- exact H.
-------------------- exact H21.
Qed.
