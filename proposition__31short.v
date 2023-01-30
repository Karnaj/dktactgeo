Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export logic.
Require Export proposition__31.
Definition proposition__31short : forall A B C D, (euclidean__axioms.BetS B D C) -> ((euclidean__axioms.nCol B C A) -> (exists X Y Z, (euclidean__axioms.BetS X A Y) /\ ((euclidean__defs.CongA X A D A D C) /\ ((euclidean__defs.Par X Y B C) /\ ((euclidean__axioms.BetS X Z C) /\ (euclidean__axioms.BetS A Z D)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (exists E F S, (euclidean__axioms.BetS E A F) /\ ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))))))))))) as H1.
- apply (@proposition__31.proposition__31 A B C D H H0).
- destruct H1 as [E H2].
destruct H2 as [F H3].
destruct H3 as [S H4].
destruct H4 as [H5 H6].
destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exists E.
exists F.
exists S.
split.
-- exact H5.
-- split.
--- exact H13.
--- split.
---- exact H19.
---- split.
----- exact H31.
----- exact H34.
Qed.
