Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export logic.
Definition lemma__collinear5 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point), (euclidean__axioms.neq A B) -> ((euclidean__axioms.Col A B C) -> ((euclidean__axioms.Col A B D) -> ((euclidean__axioms.Col A B E) -> (euclidean__axioms.Col C D E)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.Col B C D) as H3.
- apply (@euclidean__tactics.not__nCol__Col (B) (C) (D)).
--intro H3.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (D) (H3)).
---apply (@lemma__collinear4.lemma__collinear4 (A) (B) (C) (D) (H0) (H1) H).


- assert (* Cut *) (euclidean__axioms.Col B C E) as H4.
-- apply (@euclidean__tactics.not__nCol__Col (B) (C) (E)).
---intro H4.
apply (@euclidean__tactics.Col__nCol__False (B) (C) (E) (H4)).
----apply (@lemma__collinear4.lemma__collinear4 (A) (B) (C) (E) (H0) (H2) H).


-- assert (* Cut *) (euclidean__axioms.Col C D E) as H5.
--- assert (* Cut *) ((euclidean__axioms.neq B C) \/ (B = C)) as H5.
---- apply (@euclidean__tactics.neq__or__eq (B) C).
---- assert (* Cut *) ((euclidean__axioms.neq B C) \/ (B = C)) as H6.
----- exact H5.
----- assert (* Cut *) ((euclidean__axioms.neq B C) \/ (B = C)) as __TmpHyp.
------ exact H6.
------ assert (euclidean__axioms.neq B C \/ B = C) as H7.
------- exact __TmpHyp.
------- destruct H7 as [H7|H7].
-------- assert (* Cut *) (euclidean__axioms.Col C D E) as H8.
--------- apply (@euclidean__tactics.not__nCol__Col (C) (D) (E)).
----------intro H8.
apply (@euclidean__tactics.Col__nCol__False (C) (D) (E) (H8)).
-----------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (D) (E) (H3) (H4) H7).


--------- exact H8.
-------- assert (* Cut *) (euclidean__axioms.Col B D E) as H8.
--------- apply (@euclidean__tactics.not__nCol__Col (B) (D) (E)).
----------intro H8.
apply (@euclidean__tactics.Col__nCol__False (B) (D) (E) (H8)).
-----------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (D) (E) (H1) (H2) H).


--------- assert (* Cut *) (euclidean__axioms.Col C D E) as H9.
---------- apply (@eq__ind__r euclidean__axioms.Point C (fun B0: euclidean__axioms.Point => (euclidean__axioms.neq A B0) -> ((euclidean__axioms.Col A B0 C) -> ((euclidean__axioms.Col A B0 D) -> ((euclidean__axioms.Col A B0 E) -> ((euclidean__axioms.Col B0 C D) -> ((euclidean__axioms.Col B0 C E) -> ((euclidean__axioms.Col B0 D E) -> (euclidean__axioms.Col C D E))))))))) with (x := B).
-----------intro H9.
intro H10.
intro H11.
intro H12.
intro H13.
intro H14.
intro H15.
exact H15.

----------- exact H7.
----------- exact H.
----------- exact H0.
----------- exact H1.
----------- exact H2.
----------- exact H3.
----------- exact H4.
----------- exact H8.
---------- exact H9.
--- exact H5.
Qed.
