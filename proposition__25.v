Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__angletrichotomy2.
Require Export lemma__collinearorder.
Require Export lemma__congruencesymmetric.
Require Export lemma__equalanglessymmetric.
Require Export lemma__lessthancongruence2.
Require Export lemma__trichotomy2.
Require Export logic.
Require Export proposition__04.
Require Export proposition__24.
Definition proposition__25 : forall A B C D E F, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.Triangle D E F) -> ((euclidean__axioms.Cong A B D E) -> ((euclidean__axioms.Cong A C D F) -> ((euclidean__defs.Lt E F B C) -> (euclidean__defs.LtA E D F B A C))))).
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
assert (* Cut *) (euclidean__axioms.Cong D E A B) as H4.
- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D A B E H1).
- assert (* Cut *) (euclidean__axioms.Cong D F A C) as H5.
-- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric D A C F H2).
-- assert (* Cut *) (~(euclidean__defs.LtA B A C E D F)) as H6.
--- intro H6.
assert (* Cut *) (euclidean__defs.Lt B C E F) as H7.
---- apply (@proposition__24.proposition__24 D E F A B C H0 H H4 H5 H6).
---- assert (* Cut *) (~(euclidean__defs.Lt E F B C)) as H8.
----- apply (@lemma__trichotomy2.lemma__trichotomy2 B C E F H7).
----- apply (@H8 H3).
--- assert (euclidean__axioms.nCol A B C) as H7 by exact H.
assert (* Cut *) (~(euclidean__axioms.Col B A C)) as H8.
---- intro H8.
assert (* Cut *) (euclidean__axioms.Col A B C) as H9.
----- assert (* Cut *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col A C B) /\ ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col B C A) /\ (euclidean__axioms.Col C A B))))) as H9.
------ apply (@lemma__collinearorder.lemma__collinearorder B A C H8).
------ destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H10.
----- apply (@euclidean__tactics.Col__nCol__False A B C H7 H9).
---- assert (euclidean__axioms.nCol D E F) as H9 by exact H0.
assert (* Cut *) (~(euclidean__axioms.Col E D F)) as H10.
----- intro H10.
assert (* Cut *) (euclidean__axioms.Col D E F) as H11.
------ assert (* Cut *) ((euclidean__axioms.Col D E F) /\ ((euclidean__axioms.Col D F E) /\ ((euclidean__axioms.Col F E D) /\ ((euclidean__axioms.Col E F D) /\ (euclidean__axioms.Col F D E))))) as H11.
------- apply (@lemma__collinearorder.lemma__collinearorder E D F H10).
------- destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
exact H12.
------ apply (@H8).
-------apply (@euclidean__tactics.not__nCol__Col B A C).
--------intro H12.
apply (@euclidean__tactics.Col__nCol__False D E F H9 H11).


----- assert (* Cut *) (~(euclidean__defs.CongA E D F B A C)) as H11.
------ intro H11.
assert (* Cut *) (euclidean__defs.CongA B A C E D F) as H12.
------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric E D F B A C H11).
------- assert (* Cut *) (euclidean__axioms.Cong B C E F) as H13.
-------- assert (* Cut *) (forall A0 B0 C0 a b c, (euclidean__axioms.Cong A0 B0 a b) -> ((euclidean__axioms.Cong A0 C0 a c) -> ((euclidean__defs.CongA B0 A0 C0 b a c) -> (euclidean__axioms.Cong B0 C0 b c)))) as H13.
--------- intro A0.
intro B0.
intro C0.
intro a.
intro b.
intro c.
intro __.
intro __0.
intro __1.
assert (* AndElim *) ((euclidean__axioms.Cong B0 C0 b c) /\ ((euclidean__defs.CongA A0 B0 C0 a b c) /\ (euclidean__defs.CongA A0 C0 B0 a c b))) as __2.
---------- apply (@proposition__04.proposition__04 A0 B0 C0 a b c __ __0 __1).
---------- destruct __2 as [__2 __3].
exact __2.
--------- apply (@H13 A B C D E F H1 H2 H12).
-------- assert (* Cut *) (euclidean__axioms.Cong E F B C) as H14.
--------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric E B C F H13).
--------- assert (* Cut *) (euclidean__defs.Lt B C B C) as H15.
---------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 E F B C B C H3 H14).
---------- assert (* Cut *) (~(euclidean__defs.Lt B C B C)) as H16.
----------- apply (@lemma__trichotomy2.lemma__trichotomy2 B C B C H15).
----------- apply (@H8).
------------apply (@euclidean__tactics.not__nCol__Col B A C).
-------------intro H17.
apply (@H16 H15).


------ assert (* Cut *) (euclidean__defs.LtA E D F B A C) as H12.
------- apply (@lemma__angletrichotomy2.lemma__angletrichotomy2 E D F B A C).
--------apply (@euclidean__tactics.nCol__notCol E D F H10).

--------apply (@euclidean__tactics.nCol__notCol B A C H8).

-------- exact H11.
-------- exact H6.
------- exact H12.
Qed.
