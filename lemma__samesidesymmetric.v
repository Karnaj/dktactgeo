Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__NCorder.
Require Export lemma__collinearorder.
Require Export logic.
Definition lemma__samesidesymmetric : forall A B P Q, (euclidean__defs.OS P Q A B) -> ((euclidean__defs.OS Q P A B) /\ ((euclidean__defs.OS P Q B A) /\ (euclidean__defs.OS Q P B A))).
Proof.
intro A.
intro B.
intro P.
intro Q.
intro H.
assert (* Cut *) (exists E F G, (euclidean__axioms.Col A B E) /\ ((euclidean__axioms.Col A B F) /\ ((euclidean__axioms.BetS P E G) /\ ((euclidean__axioms.BetS Q F G) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H0.
- assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H0 by exact H.
assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [x H1].
destruct H1 as [x0 H2].
destruct H2 as [x1 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exists x0.
exists x1.
exists x.
split.
-- exact H4.
-- split.
--- exact H6.
--- split.
---- exact H8.
---- split.
----- exact H10.
----- split.
------ exact H12.
------ exact H13.
- destruct H0 as [E H1].
destruct H1 as [F H2].
destruct H2 as [G H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
assert (* Cut *) (euclidean__defs.OS Q P A B) as H14.
-- exists G.
exists F.
exists E.
split.
--- exact H6.
--- split.
---- exact H4.
---- split.
----- exact H10.
----- split.
------ exact H8.
------ split.
------- exact H13.
------- exact H12.
-- assert (* Cut *) (euclidean__axioms.Col B A E) as H15.
--- assert (* Cut *) ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col B E A) /\ ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col A E B) /\ (euclidean__axioms.Col E B A))))) as H15.
---- apply (@lemma__collinearorder.lemma__collinearorder A B E H4).
---- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H16.
--- assert (* Cut *) (euclidean__axioms.Col B A F) as H16.
---- assert (* Cut *) ((euclidean__axioms.Col B A F) /\ ((euclidean__axioms.Col B F A) /\ ((euclidean__axioms.Col F A B) /\ ((euclidean__axioms.Col A F B) /\ (euclidean__axioms.Col F B A))))) as H16.
----- apply (@lemma__collinearorder.lemma__collinearorder A B F H6).
----- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
exact H17.
---- assert (* Cut *) (euclidean__axioms.nCol B A P) as H17.
----- assert (* Cut *) ((euclidean__axioms.nCol B A P) /\ ((euclidean__axioms.nCol B P A) /\ ((euclidean__axioms.nCol P A B) /\ ((euclidean__axioms.nCol A P B) /\ (euclidean__axioms.nCol P B A))))) as H17.
------ apply (@lemma__NCorder.lemma__NCorder A B P H12).
------ destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H18.
----- assert (* Cut *) (euclidean__axioms.nCol B A Q) as H18.
------ assert (* Cut *) ((euclidean__axioms.nCol B A Q) /\ ((euclidean__axioms.nCol B Q A) /\ ((euclidean__axioms.nCol Q A B) /\ ((euclidean__axioms.nCol A Q B) /\ (euclidean__axioms.nCol Q B A))))) as H18.
------- apply (@lemma__NCorder.lemma__NCorder A B Q H13).
------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H19.
------ assert (* Cut *) (euclidean__defs.OS P Q B A) as H19.
------- exists G.
exists E.
exists F.
split.
-------- exact H15.
-------- split.
--------- exact H16.
--------- split.
---------- exact H8.
---------- split.
----------- exact H10.
----------- split.
------------ exact H17.
------------ exact H18.
------- assert (* Cut *) (euclidean__defs.OS Q P B A) as H20.
-------- exists G.
exists F.
exists E.
split.
--------- exact H16.
--------- split.
---------- exact H15.
---------- split.
----------- exact H10.
----------- split.
------------ exact H8.
------------ split.
------------- exact H18.
------------- exact H17.
-------- split.
--------- exact H14.
--------- split.
---------- exact H19.
---------- exact H20.
Qed.
