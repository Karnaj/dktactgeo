Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ABCequalsCBA.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export logic.
Definition lemma__equalanglesflip : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.CongA A B C D E F) -> (euclidean__defs.CongA C B A F E D).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
assert (* Cut *) (euclidean__axioms.nCol D E F) as H0.
- apply (@euclidean__tactics.nCol__notCol (D) (E) (F)).
--apply (@euclidean__tactics.nCol__not__Col (D) (E) (F)).
---apply (@lemma__equalanglesNC.lemma__equalanglesNC (A) (B) (C) (D) (E) (F) H).


- assert (* Cut *) (euclidean__defs.CongA D E F A B C) as H1.
-- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (A) (B) (C) (D) (E) (F) H).
-- assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
--- apply (@euclidean__tactics.nCol__notCol (A) (B) (C)).
----apply (@euclidean__tactics.nCol__not__Col (A) (B) (C)).
-----apply (@lemma__equalanglesNC.lemma__equalanglesNC (D) (E) (F) (A) (B) (C) H1).


--- assert (* Cut *) (~(euclidean__axioms.Col C B A)) as H3.
---- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
----- assert (* Cut *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H4.
------ apply (@lemma__collinearorder.lemma__collinearorder (C) (B) (A) H3).
------ assert (* AndElim *) ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))))) as H5.
------- exact H4.
------- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ (euclidean__axioms.Col A B C)) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
exact H12.
----- apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H2) H4).
---- assert (* Cut *) (euclidean__defs.CongA C B A A B C) as H4.
----- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (C) (B) (A)).
------apply (@euclidean__tactics.nCol__notCol (C) (B) (A) H3).

----- assert (* Cut *) (euclidean__defs.CongA C B A D E F) as H5.
------ apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (C) (B) (A) (A) (B) (C) (D) (E) (F) (H4) H).
------ assert (* Cut *) (euclidean__defs.CongA D E F F E D) as H6.
------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (D) (E) (F) H0).
------- assert (* Cut *) (euclidean__defs.CongA C B A F E D) as H7.
-------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (C) (B) (A) (D) (E) (F) (F) (E) (D) (H5) H6).
-------- exact H7.
Qed.
