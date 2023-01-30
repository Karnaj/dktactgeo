Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Require Export proposition__23B.
Definition proposition__23C : forall A B C D E P, (euclidean__axioms.neq A B) -> ((euclidean__axioms.nCol D C E) -> ((euclidean__axioms.nCol A B P) -> (exists X Y, (euclidean__defs.Out A B Y) /\ ((euclidean__defs.CongA X A Y D C E) /\ (euclidean__defs.OS X P A B))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro P.
intro H.
intro H0.
intro H1.
assert (* Cut *) (~(P = A)) as H2.
- intro H2.
assert (* Cut *) (A = P) as H3.
-- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric A P H2).
-- assert (* Cut *) (euclidean__axioms.Col A B P) as H4.
--- right.
left.
exact H3.
--- apply (@euclidean__tactics.Col__nCol__False A B P H1 H4).
- assert (* Cut *) (exists Q, (euclidean__axioms.BetS P A Q) /\ (euclidean__axioms.Cong A Q P A)) as H3.
-- apply (@lemma__extension.lemma__extension P A P A H2 H2).
-- destruct H3 as [Q H4].
destruct H4 as [H5 H6].
assert (* Cut *) (A = A) as H7.
--- apply (@logic.eq__refl Point A).
--- assert (* Cut *) (euclidean__axioms.Col A B A) as H8.
---- right.
left.
exact H7.
---- assert (* Cut *) (~(euclidean__axioms.Col A B Q)) as H9.
----- intro H9.
assert (* Cut *) (euclidean__axioms.Col P A Q) as H10.
------ right.
right.
right.
right.
left.
exact H5.
------ assert (* Cut *) (euclidean__axioms.Col Q A B) as H11.
------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H11.
-------- apply (@lemma__collinearorder.lemma__collinearorder A B Q H9).
-------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
------- assert (* Cut *) (euclidean__axioms.Col Q A P) as H12.
-------- assert (* Cut *) ((euclidean__axioms.Col A P Q) /\ ((euclidean__axioms.Col A Q P) /\ ((euclidean__axioms.Col Q P A) /\ ((euclidean__axioms.Col P Q A) /\ (euclidean__axioms.Col Q A P))))) as H12.
--------- apply (@lemma__collinearorder.lemma__collinearorder P A Q H10).
--------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H20.
-------- assert (* Cut *) (euclidean__axioms.neq A Q) as H13.
--------- assert (* Cut *) ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq P A) /\ (euclidean__axioms.neq P Q))) as H13.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal P A Q H5).
---------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
--------- assert (* Cut *) (euclidean__axioms.neq Q A) as H14.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A Q H13).
---------- assert (* Cut *) (euclidean__axioms.Col A B P) as H15.
----------- apply (@euclidean__tactics.not__nCol__Col A B P).
------------intro H15.
apply (@euclidean__tactics.Col__nCol__False A B P H15).
-------------apply (@lemma__collinear4.lemma__collinear4 Q A B P H11 H12 H14).


----------- apply (@euclidean__tactics.Col__nCol__False A B P H1 H15).
----- assert (* Cut *) (exists F G, (euclidean__defs.Out A B G) /\ ((euclidean__defs.CongA F A G D C E) /\ (euclidean__axioms.TS F A B Q))) as H10.
------ apply (@proposition__23B.proposition__23B A B C D E Q H H0).
-------apply (@euclidean__tactics.nCol__notCol A B Q H9).

------ destruct H10 as [F H11].
destruct H11 as [G H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
assert (exists J, (euclidean__axioms.BetS F J Q) /\ ((euclidean__axioms.Col A B J) /\ (euclidean__axioms.nCol A B F))) as H17 by exact H16.
destruct H17 as [J H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (* Cut *) (euclidean__defs.OS F P A B) as H23.
------- exists Q.
exists J.
exists A.
split.
-------- exact H21.
-------- split.
--------- exact H8.
--------- split.
---------- exact H19.
---------- split.
----------- exact H5.
----------- split.
------------ exact H22.
------------ exact H1.
------- exists F.
exists G.
split.
-------- exact H13.
-------- split.
--------- exact H15.
--------- exact H23.
Qed.
