Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__equalanglestransitive.
Require Export logic.
Definition lemma__angleorderrespectscongruence2 : forall A B C D E F a b c, (euclidean__defs.LtA A B C D E F) -> ((euclidean__defs.CongA a b c A B C) -> (euclidean__defs.LtA a b c D E F)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro a.
intro b.
intro c.
intro H.
intro H0.
assert (exists P Q R, (euclidean__axioms.BetS P Q R) /\ ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q)))) as H1 by exact H.
destruct H1 as [P H2].
destruct H2 as [Q H3].
destruct H3 as [R H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
assert (* Cut *) (euclidean__defs.CongA a b c D E Q) as H11.
- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive a b c A B C D E Q H0 H10).
- assert (* Cut *) (euclidean__defs.LtA a b c D E F) as H12.
-- exists P.
exists Q.
exists R.
split.
--- exact H5.
--- split.
---- exact H7.
---- split.
----- exact H9.
----- exact H11.
-- exact H12.
Qed.
