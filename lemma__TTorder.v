Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__TGsymmetric.
Require Export logic.
Definition lemma__TTorder : forall A B C D E F G H, (euclidean__defs.TT A B C D E F G H) -> (euclidean__defs.TT C D A B E F G H).
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
assert (exists J, (euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J))) as H1 by exact H0.
destruct H1 as [J H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__defs.TG C D A B E J) as H7.
- apply (@lemma__TGsymmetric.lemma__TGsymmetric A C E B D J H6).
- assert (* Cut *) (euclidean__defs.TT C D A B E F G H) as H8.
-- exists J.
split.
--- exact H3.
--- split.
---- exact H5.
---- exact H7.
-- exact H8.
Qed.
