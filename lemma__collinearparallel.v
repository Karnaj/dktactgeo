Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__collinearparallel : forall A B C c d, (euclidean__defs.Par A B c d) -> ((euclidean__axioms.Col c d C) -> ((euclidean__axioms.neq C d) -> (euclidean__defs.Par A B C d))).
Proof.
intro A.
intro B.
intro C.
intro c.
intro d.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists R a b p q, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col c d p) /\ ((euclidean__axioms.Col c d q) /\ ((euclidean__axioms.neq p q) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS a R q) /\ (euclidean__axioms.BetS p R b))))))))))) as H2.
- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H2 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col c d u) /\ ((euclidean__axioms.Col c d v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B c d)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H2.
destruct __TmpHyp as [x H3].
destruct H3 as [x0 H4].
destruct H4 as [x1 H5].
destruct H5 as [x2 H6].
destruct H6 as [x3 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exists x3.
exists x.
exists x0.
exists x1.
exists x2.
split.
-- exact H8.
-- split.
--- exact H10.
--- split.
---- exact H12.
---- split.
----- exact H14.
----- split.
------ exact H16.
------ split.
------- exact H18.
------- split.
-------- exact H20.
-------- split.
--------- exact H22.
--------- split.
---------- exact H24.
---------- split.
----------- exact H26.
----------- exact H27.
- destruct H2 as [R H3].
destruct H3 as [a H4].
destruct H4 as [b H5].
destruct H5 as [p H6].
destruct H6 as [q H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
assert (* Cut *) (euclidean__axioms.neq d C) as H28.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C d H1).
-- assert (* Cut *) (euclidean__axioms.Col d C p) as H29.
--- apply (@euclidean__tactics.not__nCol__Col d C p).
----intro H29.
apply (@euclidean__tactics.Col__nCol__False d C p H29).
-----apply (@lemma__collinear4.lemma__collinear4 c d C p H0 H18 H10).


--- assert (* Cut *) (euclidean__axioms.Col C d p) as H30.
---- assert (* Cut *) ((euclidean__axioms.Col C d p) /\ ((euclidean__axioms.Col C p d) /\ ((euclidean__axioms.Col p d C) /\ ((euclidean__axioms.Col d p C) /\ (euclidean__axioms.Col p C d))))) as H30.
----- apply (@lemma__collinearorder.lemma__collinearorder d C p H29).
----- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H31.
---- assert (* Cut *) (euclidean__axioms.Col d C q) as H31.
----- apply (@euclidean__tactics.not__nCol__Col d C q).
------intro H31.
apply (@euclidean__tactics.Col__nCol__False d C q H31).
-------apply (@lemma__collinear4.lemma__collinear4 c d C q H0 H20 H10).


----- assert (* Cut *) (euclidean__axioms.Col C d q) as H32.
------ assert (* Cut *) ((euclidean__axioms.Col C d q) /\ ((euclidean__axioms.Col C q d) /\ ((euclidean__axioms.Col q d C) /\ ((euclidean__axioms.Col d q C) /\ (euclidean__axioms.Col q C d))))) as H32.
------- apply (@lemma__collinearorder.lemma__collinearorder d C q H31).
------- destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
destruct H38 as [H39 H40].
exact H33.
------ assert (* Cut *) (~(euclidean__defs.Meet A B C d)) as H33.
------- intro H33.
assert (exists E, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C d) /\ ((euclidean__axioms.Col A B E) /\ (euclidean__axioms.Col C d E)))) as H34 by exact H33.
destruct H34 as [E H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
assert (* Cut *) (euclidean__axioms.Col C d c) as H42.
-------- assert (* Cut *) ((euclidean__axioms.Col d c C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C c d) /\ ((euclidean__axioms.Col c C d) /\ (euclidean__axioms.Col C d c))))) as H42.
--------- apply (@lemma__collinearorder.lemma__collinearorder c d C H0).
--------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H50.
-------- assert (* Cut *) (euclidean__axioms.Col d E c) as H43.
--------- apply (@euclidean__tactics.not__nCol__Col d E c).
----------intro H43.
apply (@euclidean__tactics.Col__nCol__False d E c H43).
-----------apply (@lemma__collinear4.lemma__collinear4 C d E c H41 H42 H38).


--------- assert (* Cut *) (euclidean__axioms.Col c d E) as H44.
---------- assert (* Cut *) ((euclidean__axioms.Col E d c) /\ ((euclidean__axioms.Col E c d) /\ ((euclidean__axioms.Col c d E) /\ ((euclidean__axioms.Col d c E) /\ (euclidean__axioms.Col c E d))))) as H44.
----------- apply (@lemma__collinearorder.lemma__collinearorder d E c H43).
----------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H49.
---------- assert (* Cut *) (euclidean__defs.Meet A B c d) as H45.
----------- exists E.
split.
------------ exact H36.
------------ split.
------------- exact H10.
------------- split.
-------------- exact H40.
-------------- exact H44.
----------- apply (@H24 H45).
------- assert (* Cut *) (euclidean__defs.Par A B C d) as H34.
-------- exists a.
exists b.
exists p.
exists q.
exists R.
split.
--------- exact H8.
--------- split.
---------- exact H1.
---------- split.
----------- exact H12.
----------- split.
------------ exact H14.
------------ split.
------------- exact H16.
------------- split.
-------------- exact H30.
-------------- split.
--------------- exact H32.
--------------- split.
---------------- exact H22.
---------------- split.
----------------- exact H33.
----------------- split.
------------------ exact H26.
------------------ exact H27.
-------- exact H34.
Qed.
