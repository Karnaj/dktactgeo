Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export logic.
Require Export proposition__31.
Definition proposition__31short : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.BetS B D C) -> ((euclidean__axioms.nCol B C A) -> (exists (X: euclidean__axioms.Point) (Y: euclidean__axioms.Point) (Z: euclidean__axioms.Point), (euclidean__axioms.BetS X A Y) /\ ((euclidean__defs.CongA X A D A D C) /\ ((euclidean__defs.Par X Y B C) /\ ((euclidean__axioms.BetS X Z C) /\ (euclidean__axioms.BetS A Z D)))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (exists (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (S: euclidean__axioms.Point), (euclidean__axioms.BetS E A F) /\ ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))))))))))) as H1.
- apply (@proposition__31.proposition__31 (A) (B) (C) (D) (H) H0).
- assert (exists E: euclidean__axioms.Point, (exists (F: euclidean__axioms.Point) (S: euclidean__axioms.Point), (euclidean__axioms.BetS E A F) /\ ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))))))))))) as H2.
-- exact H1.
-- destruct H2 as [E H2].
assert (exists F: euclidean__axioms.Point, (exists (S: euclidean__axioms.Point), (euclidean__axioms.BetS E A F) /\ ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))))))))))) as H3.
--- exact H2.
--- destruct H3 as [F H3].
assert (exists S: euclidean__axioms.Point, ((euclidean__axioms.BetS E A F) /\ ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))))))))))) as H4.
---- exact H3.
---- destruct H4 as [S H4].
assert (* AndElim *) ((euclidean__axioms.BetS E A F) /\ ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))))))))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.CongA F A D A D B) /\ ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))))))))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.CongA F A D B D A) /\ ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))))))))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__defs.CongA D A F B D A) /\ ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))))))) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__defs.CongA E A D A D C) /\ ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))))))) as H13.
--------- exact H12.
--------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__defs.CongA E A D C D A) /\ ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))))) as H15.
---------- exact H14.
---------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__defs.CongA D A E C D A) /\ ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))))) as H17.
----------- exact H16.
----------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__defs.Par E F B C) /\ ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))))) as H19.
------------ exact H18.
------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Cong E A D C) /\ ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))))) as H21.
------------- exact H20.
------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Cong A F B D) /\ ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))))) as H23.
-------------- exact H22.
-------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Cong A S S D) /\ ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))))) as H25.
--------------- exact H24.
--------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Cong E S S C) /\ ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))))) as H27.
---------------- exact H26.
---------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Cong B S S F) /\ ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)))) as H29.
----------------- exact H28.
----------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.BetS E S C) /\ ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D))) as H31.
------------------ exact H30.
------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.BetS B S F) /\ (euclidean__axioms.BetS A S D)) as H33.
------------------- exact H32.
------------------- destruct H33 as [H33 H34].
exists E.
exists F.
exists S.
split.
-------------------- exact H5.
-------------------- split.
--------------------- exact H13.
--------------------- split.
---------------------- exact H19.
---------------------- split.
----------------------- exact H31.
----------------------- exact H34.
Qed.
