Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__equalanglestransitive.
Require Export logic.
Definition lemma__angleorderrespectscongruence2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__defs.LtA A B C D E F) -> ((euclidean__defs.CongA a b c A B C) -> (euclidean__defs.LtA a b c D E F)).
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
assert (* Cut *) (exists (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.BetS P Q R) /\ ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q)))) as H1.
- exact H.
- assert (exists P: euclidean__axioms.Point, (exists (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.BetS P Q R) /\ ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q))))) as H2.
-- exact H1.
-- destruct H2 as [P H2].
assert (exists Q: euclidean__axioms.Point, (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS P Q R) /\ ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q))))) as H3.
--- exact H2.
--- destruct H3 as [Q H3].
assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS P Q R) /\ ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q))))) as H4.
---- exact H3.
---- destruct H4 as [R H4].
assert (* AndElim *) ((euclidean__axioms.BetS P Q R) /\ ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q)))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Out E D P) /\ ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Out E F R) /\ (euclidean__defs.CongA A B C D E Q)) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* Cut *) (euclidean__defs.CongA a b c D E Q) as H11.
-------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (a) (b) (c) (A) (B) (C) (D) (E) (Q) (H0) H10).
-------- assert (* Cut *) (euclidean__defs.LtA a b c D E F) as H12.
--------- exists P.
exists Q.
exists R.
split.
---------- exact H5.
---------- split.
----------- exact H7.
----------- split.
------------ exact H9.
------------ exact H11.
--------- exact H12.
Qed.
