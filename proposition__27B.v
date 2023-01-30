Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__angledistinct.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export logic.
Require Export proposition__27.
Definition proposition__27B : forall A D E F, (euclidean__defs.CongA A E F E F D) -> ((euclidean__axioms.TS A E F D) -> (euclidean__defs.Par A E F D)).
Proof.
intro A.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (* Cut *) (euclidean__axioms.neq A E) as H1.
- assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ (euclidean__axioms.neq E D)))))) as H1.
-- apply (@lemma__angledistinct.lemma__angledistinct A E F E F D H).
-- destruct H1 as [H2 H3].
destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H2.
- assert (* Cut *) (exists B, (euclidean__axioms.BetS A E B) /\ (euclidean__axioms.Cong E B A E)) as H2.
-- apply (@lemma__extension.lemma__extension A E A E H1 H1).
-- destruct H2 as [B H3].
destruct H3 as [H4 H5].
assert (* Cut *) (euclidean__axioms.neq F D) as H6.
--- assert (* Cut *) ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq A F) /\ ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq F D) /\ (euclidean__axioms.neq E D)))))) as H6.
---- apply (@lemma__angledistinct.lemma__angledistinct A E F E F D H).
---- destruct H6 as [H7 H8].
destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H15.
--- assert (* Cut *) (euclidean__axioms.neq D F) as H7.
---- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric F D H6).
---- assert (* Cut *) (exists C, (euclidean__axioms.BetS D F C) /\ (euclidean__axioms.Cong F C F D)) as H8.
----- apply (@lemma__extension.lemma__extension D F F D H7 H6).
----- destruct H8 as [C H9].
destruct H9 as [H10 H11].
assert (* Cut *) (euclidean__axioms.BetS C F D) as H12.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry D F C H10).
------ assert (* Cut *) (euclidean__defs.Par A B C D) as H13.
------- apply (@proposition__27.proposition__27 A B C D E F H4 H12 H H0).
------- assert (* Cut *) (euclidean__axioms.Col D F C) as H14.
-------- right.
right.
right.
right.
left.
exact H10.
-------- assert (* Cut *) (euclidean__axioms.Col C D F) as H15.
--------- assert (* Cut *) ((euclidean__axioms.Col F D C) /\ ((euclidean__axioms.Col F C D) /\ ((euclidean__axioms.Col C D F) /\ ((euclidean__axioms.Col D C F) /\ (euclidean__axioms.Col C F D))))) as H15.
---------- apply (@lemma__collinearorder.lemma__collinearorder D F C H14).
---------- destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
exact H20.
--------- assert (* Cut *) (euclidean__defs.Par A B F D) as H16.
---------- apply (@lemma__collinearparallel.lemma__collinearparallel A B F C D H13 H15 H6).
---------- assert (* Cut *) (euclidean__defs.Par F D A B) as H17.
----------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B F D H16).
----------- assert (* Cut *) (euclidean__defs.Par F D B A) as H18.
------------ assert (* Cut *) ((euclidean__defs.Par D F A B) /\ ((euclidean__defs.Par F D B A) /\ (euclidean__defs.Par D F B A))) as H18.
------------- apply (@lemma__parallelflip.lemma__parallelflip F D A B H17).
------------- destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
exact H21.
------------ assert (* Cut *) (euclidean__axioms.Col A E B) as H19.
------------- right.
right.
right.
right.
left.
exact H4.
------------- assert (* Cut *) (euclidean__axioms.Col B A E) as H20.
-------------- assert (* Cut *) ((euclidean__axioms.Col E A B) /\ ((euclidean__axioms.Col E B A) /\ ((euclidean__axioms.Col B A E) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col B E A))))) as H20.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A E B H19).
--------------- destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H25.
-------------- assert (* Cut *) (euclidean__axioms.neq A E) as H21.
--------------- assert (* Cut *) ((euclidean__axioms.neq F D) /\ ((euclidean__axioms.neq C F) /\ (euclidean__axioms.neq C D))) as H21.
---------------- apply (@lemma__betweennotequal.lemma__betweennotequal C F D H12).
---------------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H1.
--------------- assert (* Cut *) (euclidean__axioms.neq E A) as H22.
---------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A E H21).
---------------- assert (* Cut *) (euclidean__defs.Par F D E A) as H23.
----------------- apply (@lemma__collinearparallel.lemma__collinearparallel F D E B A H18 H20 H22).
----------------- assert (* Cut *) (euclidean__defs.Par F D A E) as H24.
------------------ assert (* Cut *) ((euclidean__defs.Par D F E A) /\ ((euclidean__defs.Par F D A E) /\ (euclidean__defs.Par D F A E))) as H24.
------------------- apply (@lemma__parallelflip.lemma__parallelflip F D E A H23).
------------------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
exact H27.
------------------ assert (* Cut *) (euclidean__defs.Par A E F D) as H25.
------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric F D A E H24).
------------------- exact H25.
Qed.
