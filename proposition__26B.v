Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__26helper.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglessymmetric.
Require Export lemma__trichotomy1.
Require Export logic.
Require Export proposition__04.
Definition proposition__26B : forall A B C D E F, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D E F) -> ((euclidean__defs.CongA A B C D E F) -> ((euclidean__defs.CongA B C A E F D) -> ((euclidean__axioms.Cong A B D E) -> ((euclidean__axioms.Cong B C E F) /\ ((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
assert (* Cut *) (~(euclidean__defs.Lt E F B C)) as H4.
- apply (@lemma__26helper.lemma__26helper A B C D E F H H1 H2 H3).
- assert (* Cut *) (euclidean__defs.CongA D E F A B C) as H5.
-- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric A B C D E F H1).
-- assert (* Cut *) (euclidean__defs.CongA E F D B C A) as H6.
--- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric B C A E F D H2).
--- assert (* Cut *) (euclidean__axioms.Cong D E A B) as H7.
---- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D A B E H3).
---- assert (* Cut *) (~(euclidean__defs.Lt B C E F)) as H8.
----- apply (@lemma__26helper.lemma__26helper D E F A B C H0 H5 H6 H7).
----- assert (* Cut *) (~(B = C)) as H9.
------ intro H9.
assert (* Cut *) (euclidean__axioms.Col A B C) as H10.
------- right.
right.
left.
exact H9.
------- assert (euclidean__axioms.nCol A B C) as H11 by exact H.
apply (@euclidean__tactics.Col__nCol__False A B C H11 H10).
------ assert (* Cut *) (~(E = F)) as H10.
------- intro H10.
assert (* Cut *) (euclidean__axioms.Col D E F) as H11.
-------- right.
right.
left.
exact H10.
-------- assert (euclidean__axioms.nCol D E F) as H12 by exact H0.
apply (@euclidean__tactics.Col__nCol__False D E F H12 H11).
------- assert (* Cut *) (euclidean__axioms.Cong B C E F) as H11.
-------- apply (@lemma__trichotomy1.lemma__trichotomy1 B C E F H8 H4 H9 H10).
-------- assert (* Cut *) (euclidean__axioms.Cong B A E D) as H12.
--------- assert (* Cut *) ((euclidean__axioms.Cong B A E D) /\ ((euclidean__axioms.Cong B A D E) /\ (euclidean__axioms.Cong A B E D))) as H12.
---------- apply (@lemma__congruenceflip.lemma__congruenceflip A B D E H3).
---------- destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H13.
--------- assert (* Cut *) ((euclidean__axioms.Cong A C D F) /\ ((euclidean__defs.CongA B A C E D F) /\ (euclidean__defs.CongA B C A E F D))) as H13.
---------- apply (@proposition__04.proposition__04 B A C E D F H12 H11 H1).
---------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.Cong B C E F) /\ ((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F)))).
-----------intro H14.
destruct H13 as [H15 H16].
destruct H16 as [H17 H18].
assert (* Cut *) ((euclidean__axioms.Cong B C E F) -> (((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F)) -> False)) as H19.
------------ intro H19.
intro H20.
apply (@H14).
-------------split.
-------------- exact H19.
-------------- exact H20.

------------ assert (* Cut *) (((euclidean__axioms.Cong A C D F) /\ (euclidean__defs.CongA B A C E D F)) -> False) as H20.
------------- apply (@H19 H11).
------------- assert (* Cut *) ((euclidean__axioms.Cong A C D F) -> ((euclidean__defs.CongA B A C E D F) -> False)) as H21.
-------------- intro H21.
intro H22.
apply (@H20).
---------------split.
---------------- exact H21.
---------------- exact H22.

-------------- assert (* Cut *) ((euclidean__defs.CongA B A C E D F) -> False) as H22.
--------------- apply (@H21 H15).
--------------- assert (* Cut *) (False) as H23.
---------------- apply (@H22 H17).
---------------- contradiction H23.

Qed.
