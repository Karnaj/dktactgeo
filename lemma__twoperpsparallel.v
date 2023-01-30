Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__8__2.
Require Export lemma__Euclid4.
Require Export lemma__NCdistinct.
Require Export lemma__betweennotequal.
Require Export lemma__collinearright.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__ray4.
Require Export lemma__rightangleNC.
Require Export logic.
Require Export proposition__28C.
Definition lemma__twoperpsparallel : forall A B C D, (euclidean__defs.Per A B C) -> ((euclidean__defs.Per B C D) -> ((euclidean__defs.OS A D B C) -> (euclidean__defs.Par A B C D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
- apply (@lemma__rightangleNC.lemma__rightangleNC A B C H).
- assert (* Cut *) (euclidean__axioms.neq B C) as H3.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H3.
--- apply (@lemma__NCdistinct.lemma__NCdistinct A B C H2).
--- destruct H3 as [H4 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H6.
-- assert (* Cut *) (exists E, (euclidean__axioms.BetS B C E) /\ (euclidean__axioms.Cong C E B C)) as H4.
--- apply (@lemma__extension.lemma__extension B C B C H3 H3).
--- destruct H4 as [E H5].
destruct H5 as [H6 H7].
assert (* Cut *) (euclidean__axioms.Col B C E) as H8.
---- right.
right.
right.
right.
left.
exact H6.
---- assert (* Cut *) (euclidean__axioms.neq C E) as H9.
----- assert (* Cut *) ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq B C) /\ (euclidean__axioms.neq B E))) as H9.
------ apply (@lemma__betweennotequal.lemma__betweennotequal B C E H6).
------ destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
exact H10.
----- assert (* Cut *) (euclidean__axioms.neq E C) as H10.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C E H9).
------ assert (* Cut *) (euclidean__defs.Per E C D) as H11.
------- apply (@lemma__collinearright.lemma__collinearright B C E D H0 H8 H10).
------- assert (* Cut *) (euclidean__defs.Per D C E) as H12.
-------- apply (@lemma__8__2.lemma__8__2 E C D H11).
-------- assert (* Cut *) (D = D) as H13.
--------- apply (@logic.eq__refl Point D).
--------- assert (* Cut *) (euclidean__axioms.nCol B C D) as H14.
---------- apply (@lemma__rightangleNC.lemma__rightangleNC B C D H0).
---------- assert (* Cut *) (euclidean__axioms.neq C D) as H15.
----------- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C B) /\ ((euclidean__axioms.neq D C) /\ (euclidean__axioms.neq D B)))))) as H15.
------------ apply (@lemma__NCdistinct.lemma__NCdistinct B C D H14).
------------ destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exact H18.
----------- assert (* Cut *) (euclidean__defs.Out C D D) as H16.
------------ apply (@lemma__ray4.lemma__ray4 C D D).
-------------right.
left.
exact H13.

------------- exact H15.
------------ assert (* Cut *) (euclidean__defs.Supp B C D D E) as H17.
------------- split.
-------------- exact H16.
-------------- exact H6.
------------- assert (* Cut *) (euclidean__defs.CongA A B C B C D) as H18.
-------------- apply (@lemma__Euclid4.lemma__Euclid4 A B C B C D H H0).
-------------- assert (* Cut *) (euclidean__defs.CongA B C D D C E) as H19.
--------------- apply (@lemma__Euclid4.lemma__Euclid4 B C D D C E H0 H12).
--------------- assert (* Cut *) (euclidean__defs.RT A B C B C D) as H20.
---------------- exists B.
exists C.
exists E.
exists D.
exists D.
split.
----------------- exact H17.
----------------- split.
------------------ exact H18.
------------------ exact H19.
---------------- assert (* Cut *) (euclidean__defs.Par B A C D) as H21.
----------------- apply (@proposition__28C.proposition__28C A D B C H20 H1).
----------------- assert (* Cut *) (euclidean__defs.Par C D B A) as H22.
------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric B A C D H21).
------------------ assert (* Cut *) (euclidean__defs.Par C D A B) as H23.
------------------- assert (* Cut *) ((euclidean__defs.Par D C B A) /\ ((euclidean__defs.Par C D A B) /\ (euclidean__defs.Par D C A B))) as H23.
-------------------- apply (@lemma__parallelflip.lemma__parallelflip C D B A H22).
-------------------- destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H26.
------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H24.
-------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C D A B H23).
-------------------- exact H24.
Qed.
