Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesreflexive.
Require Export lemma__ray4.
Require Export logic.
Definition proposition__13 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.BetS D B C) -> ((euclidean__axioms.nCol A B C) -> (euclidean__defs.RT C B A A B D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
assert (* Cut *) (A = A) as H1.
- apply (@logic.eq__refl (Point) A).
- assert (* Cut *) (euclidean__axioms.neq B A) as H2.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H2.
--- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
exact H9.
-- assert (* Cut *) (euclidean__defs.Out B A A) as H3.
--- apply (@lemma__ray4.lemma__ray4 (B) (A) (A)).
----right.
left.
exact H1.

---- exact H2.
--- assert (* Cut *) (euclidean__axioms.BetS C B D) as H4.
---- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (B) (C) H).
---- assert (* Cut *) (euclidean__defs.Supp C B A A D) as H5.
----- split.
------ exact H3.
------ exact H4.
----- assert (* Cut *) (euclidean__axioms.nCol C B A) as H6.
------ assert (* Cut *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H6.
------- apply (@lemma__NCorder.lemma__NCorder (A) (B) (C) H0).
------- assert (* AndElim *) ((euclidean__axioms.nCol B A C) /\ ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))))) as H7.
-------- exact H6.
-------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.nCol B C A) /\ ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)))) as H9.
--------- exact H8.
--------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.nCol C A B) /\ ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.nCol A C B) /\ (euclidean__axioms.nCol C B A)) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
exact H14.
------ assert (* Cut *) (euclidean__axioms.Col D B C) as H7.
------- right.
right.
right.
right.
left.
exact H.
------- assert (* Cut *) (euclidean__axioms.Col C B D) as H8.
-------- assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H8.
--------- apply (@lemma__collinearorder.lemma__collinearorder (D) (B) (C) H7).
--------- assert (* AndElim *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H9.
---------- exact H8.
---------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D)))) as H11.
----------- exact H10.
----------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D)) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
exact H16.
-------- assert (* Cut *) (B = B) as H9.
--------- apply (@logic.eq__refl (Point) B).
--------- assert (* Cut *) (euclidean__axioms.Col C B B) as H10.
---------- right.
right.
left.
exact H9.
---------- assert (* Cut *) (euclidean__axioms.neq D B) as H11.
----------- assert (* Cut *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C))) as H11.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal (D) (B) (C) H).
------------ assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C))) as H12.
------------- exact H11.
------------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq D B) /\ (euclidean__axioms.neq D C)) as H14.
-------------- exact H13.
-------------- destruct H14 as [H14 H15].
exact H14.
----------- assert (* Cut *) (euclidean__axioms.nCol D B A) as H12.
------------ apply (@euclidean__tactics.nCol__notCol (D) (B) (A)).
-------------apply (@euclidean__tactics.nCol__not__Col (D) (B) (A)).
--------------apply (@lemma__NChelper.lemma__NChelper (C) (B) (A) (D) (B) (H6) (H8) (H10) H11).


------------ assert (* Cut *) (euclidean__axioms.nCol A B D) as H13.
------------- assert (* Cut *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D A B) /\ (euclidean__axioms.nCol A B D))))) as H13.
-------------- apply (@lemma__NCorder.lemma__NCorder (D) (B) (A) H12).
-------------- assert (* AndElim *) ((euclidean__axioms.nCol B D A) /\ ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D A B) /\ (euclidean__axioms.nCol A B D))))) as H14.
--------------- exact H13.
--------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.nCol B A D) /\ ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D A B) /\ (euclidean__axioms.nCol A B D)))) as H16.
---------------- exact H15.
---------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.nCol A D B) /\ ((euclidean__axioms.nCol D A B) /\ (euclidean__axioms.nCol A B D))) as H18.
----------------- exact H17.
----------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.nCol D A B) /\ (euclidean__axioms.nCol A B D)) as H20.
------------------ exact H19.
------------------ destruct H20 as [H20 H21].
exact H21.
------------- assert (* Cut *) (euclidean__defs.CongA A B D A B D) as H14.
-------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (A) (B) (D) H13).
-------------- assert (* Cut *) (euclidean__defs.CongA C B A C B A) as H15.
--------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (C) (B) (A) H6).
--------------- assert (* Cut *) (euclidean__defs.RT C B A A B D) as H16.
---------------- exists C.
exists B.
exists D.
exists A.
exists A.
split.
----------------- exact H5.
----------------- split.
------------------ exact H15.
------------------ exact H14.
---------------- exact H16.
Qed.
