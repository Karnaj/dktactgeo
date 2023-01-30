Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__ETreflexive.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelNC.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__37.
Definition proposition__41 : forall A B C D E, (euclidean__defs.PG A B C D) -> ((euclidean__axioms.Col A D E) -> (euclidean__axioms.ET A B C E B C)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
assert (* Cut *) (euclidean__defs.Par A B C D) as H1.
- destruct H as [H1 H2].
exact H1.
- assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
-- assert (* Cut *) ((euclidean__axioms.nCol A B C) /\ ((euclidean__axioms.nCol A C D) /\ ((euclidean__axioms.nCol B C D) /\ (euclidean__axioms.nCol A B D)))) as H2.
--- apply (@lemma__parallelNC.lemma__parallelNC A B C D H1).
--- destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
exact H3.
-- assert (euclidean__axioms.Triangle A B C) as H3 by exact H2.
assert (* Cut *) (euclidean__axioms.ET A B C E B C) as H4.
--- assert (* Cut *) ((A = E) \/ (euclidean__axioms.neq A E)) as H4.
---- apply (@euclidean__tactics.eq__or__neq A E).
---- assert ((A = E) \/ (euclidean__axioms.neq A E)) as H5 by exact H4.
assert ((A = E) \/ (euclidean__axioms.neq A E)) as __TmpHyp by exact H5.
destruct __TmpHyp as [H6|H6].
----- assert (* Cut *) (euclidean__axioms.ET A B C A B C) as H7.
------ apply (@lemma__ETreflexive.lemma__ETreflexive A B C H3).
------ assert (* Cut *) (euclidean__axioms.ET A B C E B C) as H8.
------- apply (@eq__ind__r euclidean__axioms.Point E (fun A0 => (euclidean__defs.PG A0 B C D) -> ((euclidean__axioms.Col A0 D E) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.Triangle A0 B C) -> ((euclidean__axioms.ET A0 B C A0 B C) -> (euclidean__axioms.ET A0 B C E B C)))))))) with (x := A).
--------intro H8.
intro H9.
intro H10.
intro H11.
intro H12.
intro H13.
exact H13.

-------- exact H6.
-------- exact H.
-------- exact H0.
-------- exact H1.
-------- exact H2.
-------- exact H3.
-------- exact H7.
------- exact H8.
----- assert (* Cut *) (euclidean__defs.Par A D B C) as H7.
------ destruct H as [H7 H8].
exact H8.
------ assert (* Cut *) (euclidean__axioms.Col D A E) as H8.
------- assert (* Cut *) ((euclidean__axioms.Col D A E) /\ ((euclidean__axioms.Col D E A) /\ ((euclidean__axioms.Col E A D) /\ ((euclidean__axioms.Col A E D) /\ (euclidean__axioms.Col E D A))))) as H8.
-------- apply (@lemma__collinearorder.lemma__collinearorder A D E H0).
-------- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H9.
------- assert (* Cut *) (euclidean__defs.Par B C A D) as H9.
-------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A D B C H7).
-------- assert (* Cut *) (euclidean__defs.Par B C D A) as H10.
--------- assert (* Cut *) ((euclidean__defs.Par C B A D) /\ ((euclidean__defs.Par B C D A) /\ (euclidean__defs.Par C B D A))) as H10.
---------- apply (@lemma__parallelflip.lemma__parallelflip B C A D H9).
---------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H13.
--------- assert (* Cut *) (euclidean__axioms.neq E A) as H11.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H6).
---------- assert (* Cut *) (euclidean__defs.Par B C E A) as H12.
----------- apply (@lemma__collinearparallel.lemma__collinearparallel B C E D A H10 H8 H11).
----------- assert (* Cut *) (euclidean__defs.Par B C A E) as H13.
------------ assert (* Cut *) ((euclidean__defs.Par C B E A) /\ ((euclidean__defs.Par B C A E) /\ (euclidean__defs.Par C B A E))) as H13.
------------- apply (@lemma__parallelflip.lemma__parallelflip B C E A H12).
------------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H16.
------------ assert (* Cut *) (euclidean__defs.Par A E B C) as H14.
------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B C A E H13).
------------- assert (* Cut *) (euclidean__axioms.ET A B C E B C) as H15.
-------------- apply (@proposition__37.proposition__37 A B C E H14).
-------------- exact H15.
--- exact H4.
Qed.
