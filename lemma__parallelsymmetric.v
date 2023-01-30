Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export logic.
Definition lemma__parallelsymmetric : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.Par A B C D) -> (euclidean__defs.Par C D A B).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) (exists (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H0.
- exact H.
- assert (exists a: euclidean__axioms.Point, (exists (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H1.
-- exact H0.
-- destruct H1 as [a H1].
assert (exists b: euclidean__axioms.Point, (exists (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H2.
--- exact H1.
--- destruct H2 as [b H2].
assert (exists c: euclidean__axioms.Point, (exists (d: euclidean__axioms.Point) (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H3.
---- exact H2.
---- destruct H3 as [c H3].
assert (exists d: euclidean__axioms.Point, (exists (m: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H4.
----- exact H3.
----- destruct H4 as [d H4].
assert (exists m: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))))) as H5.
------ exact H4.
------ destruct H5 as [m H5].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))))) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))))) as H18.
------------- exact H17.
------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.BetS a m d) /\ (euclidean__axioms.BetS c m b)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
assert (* Cut *) (~(euclidean__defs.Meet C D A B)) as H26.
----------------- intro H26.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D P) /\ (euclidean__axioms.Col A B P)))) as H27.
------------------ exact H26.
------------------ assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D P) /\ (euclidean__axioms.Col A B P))))) as H28.
------------------- exact H27.
------------------- destruct H28 as [P H28].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D P) /\ (euclidean__axioms.Col A B P)))) as H29.
-------------------- exact H28.
-------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.Col C D P) /\ (euclidean__axioms.Col A B P))) as H31.
--------------------- exact H30.
--------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col C D P) /\ (euclidean__axioms.Col A B P)) as H33.
---------------------- exact H32.
---------------------- destruct H33 as [H33 H34].
assert (* Cut *) (euclidean__defs.Meet A B C D) as H35.
----------------------- exists P.
split.
------------------------ exact H31.
------------------------ split.
------------------------- exact H29.
------------------------- split.
-------------------------- exact H34.
-------------------------- exact H33.
----------------------- apply (@H22 H35).
----------------- assert (* Cut *) (euclidean__defs.Par C D A B) as H27.
------------------ exists c.
exists d.
exists a.
exists b.
exists m.
split.
------------------- exact H8.
------------------- split.
-------------------- exact H6.
-------------------- split.
--------------------- exact H16.
--------------------- split.
---------------------- exact H18.
---------------------- split.
----------------------- exact H20.
----------------------- split.
------------------------ exact H10.
------------------------ split.
------------------------- exact H12.
------------------------- split.
-------------------------- exact H14.
-------------------------- split.
--------------------------- exact H26.
--------------------------- split.
---------------------------- exact H25.
---------------------------- exact H24.
------------------ exact H27.
Qed.
