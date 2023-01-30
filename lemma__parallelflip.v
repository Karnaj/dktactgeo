Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__collinearorder.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__parallelflip : forall A B C D, (euclidean__defs.Par A B C D) -> ((euclidean__defs.Par B A C D) /\ ((euclidean__defs.Par A B D C) /\ (euclidean__defs.Par B A D C))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (exists M a b c d, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a M d) /\ (euclidean__axioms.BetS c M b))))))))))) as H0.
- assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H0 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [x H1].
destruct H1 as [x0 H2].
destruct H2 as [x1 H3].
destruct H3 as [x2 H4].
destruct H4 as [x3 H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
exists x3.
exists x.
exists x0.
exists x1.
exists x2.
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
------ split.
------- exact H16.
------- split.
-------- exact H18.
-------- split.
--------- exact H20.
--------- split.
---------- exact H22.
---------- split.
----------- exact H24.
----------- exact H25.
- destruct H0 as [M H1].
destruct H1 as [a H2].
destruct H2 as [b H3].
destruct H3 as [c H4].
destruct H4 as [d H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__axioms.Col B A a) as H26.
-- assert (* Cut *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H26.
--- apply (@lemma__collinearorder.lemma__collinearorder A B a H10).
--- destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H27.
-- assert (* Cut *) (euclidean__axioms.Col B A b) as H27.
--- assert (* Cut *) ((euclidean__axioms.Col B A b) /\ ((euclidean__axioms.Col B b A) /\ ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A))))) as H27.
---- apply (@lemma__collinearorder.lemma__collinearorder A B b H12).
---- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H28.
--- assert (* Cut *) (euclidean__axioms.Col D C c) as H28.
---- assert (* Cut *) ((euclidean__axioms.Col D C c) /\ ((euclidean__axioms.Col D c C) /\ ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C))))) as H28.
----- apply (@lemma__collinearorder.lemma__collinearorder C D c H16).
----- destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H29.
---- assert (* Cut *) (euclidean__axioms.Col D C d) as H29.
----- assert (* Cut *) ((euclidean__axioms.Col D C d) /\ ((euclidean__axioms.Col D d C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C))))) as H29.
------ apply (@lemma__collinearorder.lemma__collinearorder C D d H18).
------ destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H30.
----- assert (* Cut *) (euclidean__axioms.neq B A) as H30.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H6).
------ assert (* Cut *) (euclidean__axioms.neq D C) as H31.
------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C D H8).
------- assert (* Cut *) (euclidean__axioms.BetS d M a) as H32.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry a M d H24).
-------- assert (* Cut *) (euclidean__axioms.BetS b M c) as H33.
--------- apply (@euclidean__axioms.axiom__betweennesssymmetry c M b H25).
--------- assert (* Cut *) (euclidean__axioms.neq d c) as H34.
---------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric c d H20).
---------- assert (* Cut *) (euclidean__axioms.neq b a) as H35.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric a b H14).
----------- assert (* Cut *) (~(euclidean__defs.Meet A B D C)) as H36.
------------ intro H36.
assert (exists P, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col D C P)))) as H37 by exact H36.
destruct H37 as [P H38].
destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Col C D P) as H45.
------------- assert (* Cut *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H45.
-------------- apply (@lemma__collinearorder.lemma__collinearorder D C P H44).
-------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
exact H46.
------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H46.
-------------- exists P.
split.
--------------- exact H39.
--------------- split.
---------------- exact H8.
---------------- split.
----------------- exact H43.
----------------- exact H45.
-------------- apply (@H22 H46).
------------ assert (* Cut *) (~(euclidean__defs.Meet B A C D)) as H37.
------------- intro H37.
assert (exists P, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col C D P)))) as H38 by exact H37.
destruct H38 as [P H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
assert (* Cut *) (euclidean__axioms.Col A B P) as H46.
-------------- assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H46.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B A P H44).
--------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H47.
-------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H47.
--------------- exists P.
split.
---------------- exact H6.
---------------- split.
----------------- exact H42.
----------------- split.
------------------ exact H46.
------------------ exact H45.
--------------- apply (@H22 H47).
------------- assert (* Cut *) (~(euclidean__defs.Meet B A D C)) as H38.
-------------- intro H38.
assert (exists P, (euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.Col B A P) /\ (euclidean__axioms.Col D C P)))) as H39 by exact H38.
destruct H39 as [P H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
assert (* Cut *) (euclidean__axioms.Col A B P) as H47.
--------------- assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H47.
---------------- apply (@lemma__collinearorder.lemma__collinearorder B A P H45).
---------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H48.
--------------- assert (* Cut *) (euclidean__axioms.Col C D P) as H48.
---------------- assert (* Cut *) ((euclidean__axioms.Col C D P) /\ ((euclidean__axioms.Col C P D) /\ ((euclidean__axioms.Col P D C) /\ ((euclidean__axioms.Col D P C) /\ (euclidean__axioms.Col P C D))))) as H48.
----------------- apply (@lemma__collinearorder.lemma__collinearorder D C P H46).
----------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H49.
---------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H49.
----------------- exists P.
split.
------------------ exact H6.
------------------ split.
------------------- exact H8.
------------------- split.
-------------------- exact H47.
-------------------- exact H48.
----------------- apply (@H22 H49).
-------------- assert (* Cut *) (euclidean__defs.Par B A C D) as H39.
--------------- exists b.
exists a.
exists d.
exists c.
exists M.
split.
---------------- exact H30.
---------------- split.
----------------- exact H8.
----------------- split.
------------------ exact H27.
------------------ split.
------------------- exact H26.
------------------- split.
-------------------- exact H35.
-------------------- split.
--------------------- exact H18.
--------------------- split.
---------------------- exact H16.
---------------------- split.
----------------------- exact H34.
----------------------- split.
------------------------ exact H37.
------------------------ split.
------------------------- exact H33.
------------------------- exact H32.
--------------- assert (* Cut *) (euclidean__defs.Par A B D C) as H40.
---------------- exists b.
exists a.
exists d.
exists c.
exists M.
split.
----------------- exact H6.
----------------- split.
------------------ exact H31.
------------------ split.
------------------- exact H12.
------------------- split.
-------------------- exact H10.
-------------------- split.
--------------------- exact H35.
--------------------- split.
---------------------- exact H29.
---------------------- split.
----------------------- exact H28.
----------------------- split.
------------------------ exact H34.
------------------------ split.
------------------------- exact H36.
------------------------- split.
-------------------------- exact H33.
-------------------------- exact H32.
---------------- assert (* Cut *) (euclidean__defs.Par B A D C) as H41.
----------------- exists b.
exists a.
exists d.
exists c.
exists M.
split.
------------------ exact H30.
------------------ split.
------------------- exact H31.
------------------- split.
-------------------- exact H27.
-------------------- split.
--------------------- exact H26.
--------------------- split.
---------------------- exact H35.
---------------------- split.
----------------------- exact H29.
----------------------- split.
------------------------ exact H28.
------------------------ split.
------------------------- exact H34.
------------------------- split.
-------------------------- exact H38.
-------------------------- split.
--------------------------- exact H33.
--------------------------- exact H32.
----------------- split.
------------------ exact H39.
------------------ split.
------------------- exact H40.
------------------- exact H41.
Qed.
