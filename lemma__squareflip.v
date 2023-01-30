Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__congruenceflip.
Require Export logic.
Definition lemma__squareflip : forall A B C D, (euclidean__defs.SQ A B C D) -> (euclidean__defs.SQ B A D C).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H0.
- assert ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as H0 by exact H.
assert ((euclidean__axioms.Cong A B C D) /\ ((euclidean__axioms.Cong A B B C) /\ ((euclidean__axioms.Cong A B D A) /\ ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ (euclidean__defs.Per C D A))))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
split.
-- exact H1.
-- split.
--- exact H3.
--- split.
---- exact H5.
---- split.
----- exact H7.
----- split.
------ exact H9.
------ split.
------- exact H11.
------- exact H12.
- assert (* Cut *) (euclidean__axioms.Cong B A D C) as H1.
-- destruct H0 as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
assert (* Cut *) ((euclidean__axioms.Cong B A D C) /\ ((euclidean__axioms.Cong B A C D) /\ (euclidean__axioms.Cong A B D C))) as H13.
--- apply (@lemma__congruenceflip.lemma__congruenceflip A B C D H1).
--- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
-- assert (* Cut *) (euclidean__axioms.Cong B A A D) as H2.
--- destruct H0 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
assert (* Cut *) ((euclidean__axioms.Cong B A A D) /\ ((euclidean__axioms.Cong B A D A) /\ (euclidean__axioms.Cong A B A D))) as H14.
---- apply (@lemma__congruenceflip.lemma__congruenceflip A B D A H6).
---- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
--- assert (* Cut *) (euclidean__axioms.Cong B A C B) as H3.
---- destruct H0 as [H3 H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
assert (* Cut *) ((euclidean__axioms.Cong B A C B) /\ ((euclidean__axioms.Cong B A B C) /\ (euclidean__axioms.Cong A B C B))) as H15.
----- apply (@lemma__congruenceflip.lemma__congruenceflip A B B C H5).
----- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H16.
---- assert (* Cut *) (euclidean__defs.Per C B A) as H4.
----- destruct H0 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
apply (@lemma__8__2.lemma__8__2 A B C H12).
----- assert (* Cut *) (euclidean__defs.Per B A D) as H5.
------ destruct H0 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
apply (@lemma__8__2.lemma__8__2 D A B H11).
------ assert (* Cut *) (euclidean__defs.Per A D C) as H6.
------- destruct H0 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
apply (@lemma__8__2.lemma__8__2 C D A H17).
------- assert (* Cut *) (euclidean__defs.Per D C B) as H7.
-------- destruct H0 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
apply (@lemma__8__2.lemma__8__2 B C D H17).
-------- assert (* Cut *) (euclidean__defs.SQ B A D C) as H8.
--------- split.
---------- exact H1.
---------- split.
----------- exact H2.
----------- split.
------------ exact H3.
------------ split.
------------- exact H4.
------------- split.
-------------- exact H5.
-------------- split.
--------------- exact H6.
--------------- exact H7.
--------- exact H8.
Qed.
