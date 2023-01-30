Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__planeseparation.
Require Export logic.
Definition lemma__samesidetransitive : forall A B P Q R, (euclidean__defs.OS P Q A B) -> ((euclidean__defs.OS Q R A B) -> (euclidean__defs.OS P R A B)).
Proof.
intro A.
intro B.
intro P.
intro Q.
intro R.
intro H.
intro H0.
assert (* Cut *) (exists E F G, (euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS Q E G) /\ ((euclidean__axioms.BetS R F G) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as H1.
- assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as H1 by exact H0.
assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS Q U X) /\ ((euclidean__axioms.BetS R V X) /\ ((euclidean__axioms.nCol A B Q) /\ (euclidean__axioms.nCol A B R)))))) as __TmpHyp by exact H1.
destruct __TmpHyp as [x H2].
destruct H2 as [x0 H3].
destruct H3 as [x1 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H15 by exact H.
assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as __TmpHyp0 by exact H15.
destruct __TmpHyp0 as [x2 H16].
destruct H16 as [x3 H17].
destruct H17 as [x4 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exists x0.
exists x1.
exists x.
split.
-- exact H5.
-- split.
--- exact H7.
--- split.
---- exact H9.
---- split.
----- exact H11.
----- split.
------ exact H28.
------ exact H14.
- destruct H1 as [E H2].
destruct H2 as [F H3].
destruct H3 as [G H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
assert (* Cut *) (euclidean__axioms.TS Q A B G) as H15.
-- exists E.
split.
--- exact H9.
--- split.
---- exact H5.
---- exact H13.
-- assert (* Cut *) (euclidean__axioms.TS P A B G) as H16.
--- apply (@lemma__planeseparation.lemma__planeseparation A B P Q G H H15).
--- assert (exists M, (euclidean__axioms.BetS P M G) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.nCol A B P))) as H17 by exact H16.
destruct H17 as [M H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
assert (* Cut *) (euclidean__defs.OS P R A B) as H23.
---- exists G.
exists M.
exists F.
split.
----- exact H21.
----- split.
------ exact H7.
------ split.
------- exact H19.
------- split.
-------- exact H11.
-------- split.
--------- exact H22.
--------- exact H14.
---- exact H23.
Qed.
