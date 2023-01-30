Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__NChelper : forall A B C P Q, (euclidean__axioms.nCol A B C) -> ((euclidean__axioms.Col A B P) -> ((euclidean__axioms.Col A B Q) -> ((euclidean__axioms.neq P Q) -> (euclidean__axioms.nCol P Q C)))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (~(A = B)) as H3.
- intro H3.
assert (* Cut *) (euclidean__axioms.Col A B C) as H4.
-- left.
exact H3.
-- apply (@euclidean__tactics.Col__nCol__False A B C H H4).
- assert (* Cut *) (euclidean__axioms.Col B P Q) as H4.
-- apply (@euclidean__tactics.not__nCol__Col B P Q).
---intro H4.
apply (@euclidean__tactics.Col__nCol__False B P Q H4).
----apply (@lemma__collinear4.lemma__collinear4 A B P Q H0 H1 H3).


-- assert (* Cut *) (euclidean__axioms.neq B A) as H5.
--- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H3).
--- assert (* Cut *) (euclidean__axioms.Col B A P) as H6.
---- assert (* Cut *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H6.
----- apply (@lemma__collinearorder.lemma__collinearorder A B P H0).
----- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
exact H7.
---- assert (* Cut *) (euclidean__axioms.Col B A Q) as H7.
----- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H7.
------ apply (@lemma__collinearorder.lemma__collinearorder A B Q H1).
------ destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exact H8.
----- assert (* Cut *) (euclidean__axioms.Col A P Q) as H8.
------ apply (@euclidean__tactics.not__nCol__Col A P Q).
-------intro H8.
apply (@euclidean__tactics.Col__nCol__False A P Q H8).
--------apply (@lemma__collinear4.lemma__collinear4 B A P Q H6 H7 H5).


------ assert (* Cut *) (euclidean__axioms.Col P Q A) as H9.
------- assert (* Cut *) ((euclidean__axioms.Col P A Q) /\ ((euclidean__axioms.Col P Q A) /\ ((euclidean__axioms.Col Q A P) /\ ((euclidean__axioms.Col A Q P) /\ (euclidean__axioms.Col Q P A))))) as H9.
-------- apply (@lemma__collinearorder.lemma__collinearorder A P Q H8).
-------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H12.
------- assert (* Cut *) (euclidean__axioms.Col P Q B) as H10.
-------- assert (* Cut *) ((euclidean__axioms.Col P B Q) /\ ((euclidean__axioms.Col P Q B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B Q P) /\ (euclidean__axioms.Col Q P B))))) as H10.
--------- apply (@lemma__collinearorder.lemma__collinearorder B P Q H4).
--------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H13.
-------- assert (* Cut *) (~(euclidean__axioms.Col P Q C)) as H11.
--------- intro H11.
assert (* Cut *) (euclidean__axioms.Col A B C) as H12.
---------- apply (@euclidean__tactics.not__nCol__Col A B C).
-----------intro H12.
apply (@euclidean__tactics.Col__nCol__False A B C H12).
------------apply (@lemma__collinear5.lemma__collinear5 P Q A B C H2 H9 H10 H11).


---------- apply (@euclidean__tactics.Col__nCol__False A B C H H12).
--------- apply (@euclidean__tactics.nCol__notCol P Q C H11).
Qed.
