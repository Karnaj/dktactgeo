Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__TGflip.
Require Export lemma__TGsymmetric.
Require Export logic.
Definition lemma__TTflip : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.TT A B C D E F G H) -> (euclidean__defs.TT B A D C E F G H).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro H0.
assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J))) as H1.
- exact H0.
- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J)))) as H2.
-- exact H1.
-- destruct H2 as [J H2].
assert (* AndElim *) ((euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J))) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J)) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* Cut *) (euclidean__defs.TG B A C D E J) as H7.
----- assert (* Cut *) ((euclidean__defs.TG B A C D E J) /\ (euclidean__defs.TG A B C D J E)) as H7.
------ apply (@lemma__TGflip.lemma__TGflip (A) (C) (E) (B) (D) (J) H6).
------ assert (* AndElim *) ((euclidean__defs.TG B A C D E J) /\ (euclidean__defs.TG A B C D J E)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
exact H8.
----- assert (* Cut *) (euclidean__defs.TG C D B A E J) as H8.
------ apply (@lemma__TGsymmetric.lemma__TGsymmetric (B) (C) (E) (A) (D) (J) H7).
------ assert (* Cut *) (euclidean__defs.TG D C B A E J) as H9.
------- assert (* Cut *) ((euclidean__defs.TG D C B A E J) /\ (euclidean__defs.TG C D B A J E)) as H9.
-------- apply (@lemma__TGflip.lemma__TGflip (C) (B) (E) (D) (A) (J) H8).
-------- assert (* AndElim *) ((euclidean__defs.TG D C B A E J) /\ (euclidean__defs.TG C D B A J E)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
exact H10.
------- assert (* Cut *) (euclidean__defs.TG B A D C E J) as H10.
-------- apply (@lemma__TGsymmetric.lemma__TGsymmetric (D) (B) (E) (C) (A) (J) H9).
-------- assert (* Cut *) (euclidean__defs.TT B A D C E F G H) as H11.
--------- exists J.
split.
---------- exact H3.
---------- split.
----------- exact H5.
----------- exact H10.
--------- exact H11.
Qed.
