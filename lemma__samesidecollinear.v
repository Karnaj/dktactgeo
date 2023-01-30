Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__samesidecollinear : forall A B C P Q, (euclidean__defs.OS P Q A B) -> ((euclidean__axioms.Col A B C) -> ((euclidean__axioms.neq A C) -> (euclidean__defs.OS P Q A C))).
Proof.
intro A.
intro B.
intro C.
intro P.
intro Q.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists p q r, (euclidean__axioms.Col A B p) /\ ((euclidean__axioms.Col A B q) /\ ((euclidean__axioms.BetS P p r) /\ ((euclidean__axioms.BetS Q q r) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H2.
- assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as H2 by exact H.
assert (exists X U V, (euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.BetS P U X) /\ ((euclidean__axioms.BetS Q V X) /\ ((euclidean__axioms.nCol A B P) /\ (euclidean__axioms.nCol A B Q)))))) as __TmpHyp by exact H2.
destruct __TmpHyp as [x H3].
destruct H3 as [x0 H4].
destruct H4 as [x1 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
exists x0.
exists x1.
exists x.
split.
-- exact H6.
-- split.
--- exact H8.
--- split.
---- exact H10.
---- split.
----- exact H12.
----- split.
------ exact H14.
------ exact H15.
- destruct H2 as [p H3].
destruct H3 as [q H4].
destruct H4 as [r H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
assert (* Cut *) (euclidean__axioms.neq A B) as H16.
-- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq A Q) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq Q B) /\ (euclidean__axioms.neq Q A)))))) as H16.
--- apply (@lemma__NCdistinct.lemma__NCdistinct A B Q H15).
--- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
exact H17.
-- assert (* Cut *) (A = A) as H17.
--- apply (@logic.eq__refl Point A).
--- assert (* Cut *) (euclidean__axioms.Col A B A) as H18.
---- right.
left.
exact H17.
---- assert (* Cut *) (euclidean__axioms.nCol A C P) as H19.
----- apply (@euclidean__tactics.nCol__notCol A C P).
------apply (@euclidean__tactics.nCol__not__Col A C P).
-------apply (@lemma__NChelper.lemma__NChelper A B P A C H14 H18 H0 H1).


----- assert (* Cut *) (euclidean__axioms.nCol A C Q) as H20.
------ apply (@euclidean__tactics.nCol__notCol A C Q).
-------apply (@euclidean__tactics.nCol__not__Col A C Q).
--------apply (@lemma__NChelper.lemma__NChelper A B Q A C H15 H18 H0 H1).


------ assert (* Cut *) (euclidean__axioms.Col B A p) as H21.
------- assert (* Cut *) ((euclidean__axioms.Col B A p) /\ ((euclidean__axioms.Col B p A) /\ ((euclidean__axioms.Col p A B) /\ ((euclidean__axioms.Col A p B) /\ (euclidean__axioms.Col p B A))))) as H21.
-------- apply (@lemma__collinearorder.lemma__collinearorder A B p H6).
-------- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
exact H22.
------- assert (* Cut *) (euclidean__axioms.Col B A C) as H22.
-------- assert (* Cut *) ((euclidean__axioms.Col B A C) /\ ((euclidean__axioms.Col B C A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A C B) /\ (euclidean__axioms.Col C B A))))) as H22.
--------- apply (@lemma__collinearorder.lemma__collinearorder A B C H0).
--------- destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
exact H23.
-------- assert (* Cut *) (euclidean__axioms.neq B A) as H23.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H16).
--------- assert (* Cut *) (euclidean__axioms.Col A C p) as H24.
---------- apply (@euclidean__tactics.not__nCol__Col A C p).
-----------intro H24.
apply (@euclidean__tactics.Col__nCol__False A C p H24).
------------apply (@lemma__collinear4.lemma__collinear4 B A C p H22 H21 H23).


---------- assert (* Cut *) (euclidean__axioms.Col B A q) as H25.
----------- assert (* Cut *) ((euclidean__axioms.Col B A q) /\ ((euclidean__axioms.Col B q A) /\ ((euclidean__axioms.Col q A B) /\ ((euclidean__axioms.Col A q B) /\ (euclidean__axioms.Col q B A))))) as H25.
------------ apply (@lemma__collinearorder.lemma__collinearorder A B q H8).
------------ destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H26.
----------- assert (* Cut *) (euclidean__axioms.Col A C q) as H26.
------------ apply (@euclidean__tactics.not__nCol__Col A C q).
-------------intro H26.
apply (@euclidean__tactics.Col__nCol__False A C q H26).
--------------apply (@lemma__collinear4.lemma__collinear4 B A C q H22 H25 H23).


------------ assert (* Cut *) (euclidean__defs.OS P Q A C) as H27.
------------- exists r.
exists p.
exists q.
split.
-------------- exact H24.
-------------- split.
--------------- exact H26.
--------------- split.
---------------- exact H10.
---------------- split.
----------------- exact H12.
----------------- split.
------------------ exact H19.
------------------ exact H20.
------------- exact H27.
Qed.
