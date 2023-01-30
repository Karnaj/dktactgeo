Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__betweennesspreserved.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__interior5.
Require Export logic.
Definition lemma__fiveline : forall A B C D a b c d, (euclidean__axioms.Col A B C) -> ((euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong B C b c) -> ((euclidean__axioms.Cong A D a d) -> ((euclidean__axioms.Cong C D c d) -> ((euclidean__axioms.Cong A C a c) -> ((euclidean__axioms.neq A C) -> (euclidean__axioms.Cong B D b d))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro a.
intro b.
intro c.
intro d.
intro H.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
assert ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H6 by exact H.
assert (* Cut *) (euclidean__axioms.Cong B D b d) as H7.
- assert (* Cut *) ((A = B) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))) as H7.
-- apply (@euclidean__tactics.NNPP ((A = B) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))).
---intro H7.
destruct H6 as [H8|H8].
---- assert (* Cut *) ((A = B) -> False) as H9.
----- intro H9.
apply (@H7).
------left.
exact H9.

----- assert (* Cut *) (((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) -> False) as H10.
------ intro H10.
apply (@H7).
-------right.
exact H10.

------ assert (* Cut *) (False) as H11.
------- apply (@H9 H8).
------- assert (* Cut *) ((B = C) -> False) as H12.
-------- intro H12.
apply (@H10).
---------left.
exact H12.

-------- assert (* Cut *) (((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) -> False) as H13.
--------- intro H13.
apply (@H10).
----------right.
exact H13.

--------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H14.
---------- intro H14.
apply (@H13).
-----------left.
exact H14.

---------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H15.
----------- intro H15.
apply (@H13).
------------right.
exact H15.

----------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H16.
------------ intro H16.
apply (@H15).
-------------left.
exact H16.

------------ assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H17.
------------- intro H17.
apply (@H15).
--------------right.
exact H17.

------------- contradiction H11.
---- destruct H8 as [H9|H9].
----- assert (* Cut *) (False) as H10.
------ apply (@H5 H9).
------ assert (* Cut *) ((A = B) -> False) as H11.
------- intro H11.
apply (@H7).
--------left.
exact H11.

------- assert (* Cut *) (((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) -> False) as H12.
-------- intro H12.
apply (@H7).
---------right.
exact H12.

-------- assert (* Cut *) ((B = C) -> False) as H13.
--------- intro H13.
apply (@H12).
----------left.
exact H13.

--------- assert (* Cut *) (((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) -> False) as H14.
---------- intro H14.
apply (@H12).
-----------right.
exact H14.

---------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H15.
----------- intro H15.
apply (@H14).
------------left.
exact H15.

----------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H16.
------------ intro H16.
apply (@H14).
-------------right.
exact H16.

------------ assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H17.
------------- intro H17.
apply (@H16).
--------------left.
exact H17.

------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H18.
-------------- intro H18.
apply (@H16).
---------------right.
exact H18.

-------------- contradiction H10.
----- destruct H9 as [H10|H10].
------ assert (* Cut *) ((A = B) -> False) as H11.
------- intro H11.
apply (@H7).
--------left.
exact H11.

------- assert (* Cut *) (((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) -> False) as H12.
-------- intro H12.
apply (@H7).
---------right.
exact H12.

-------- assert (* Cut *) ((B = C) -> False) as H13.
--------- intro H13.
apply (@H12).
----------left.
exact H13.

--------- assert (* Cut *) (((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) -> False) as H14.
---------- intro H14.
apply (@H12).
-----------right.
exact H14.

---------- assert (* Cut *) (False) as H15.
----------- apply (@H13 H10).
----------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H16.
------------ intro H16.
apply (@H14).
-------------left.
exact H16.

------------ assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H17.
------------- intro H17.
apply (@H14).
--------------right.
exact H17.

------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H18.
-------------- intro H18.
apply (@H17).
---------------left.
exact H18.

-------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H19.
--------------- intro H19.
apply (@H17).
----------------right.
exact H19.

--------------- contradiction H15.
------ destruct H10 as [H11|H11].
------- assert (* Cut *) ((A = B) -> False) as H12.
-------- intro H12.
apply (@H7).
---------left.
exact H12.

-------- assert (* Cut *) (((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) -> False) as H13.
--------- intro H13.
apply (@H7).
----------right.
exact H13.

--------- assert (* Cut *) ((B = C) -> False) as H14.
---------- intro H14.
apply (@H13).
-----------left.
exact H14.

---------- assert (* Cut *) (((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) -> False) as H15.
----------- intro H15.
apply (@H13).
------------right.
exact H15.

----------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H16.
------------ intro H16.
apply (@H15).
-------------left.
exact H16.

------------ assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H17.
------------- intro H17.
apply (@H15).
--------------right.
exact H17.

------------- assert (* Cut *) (False) as H18.
-------------- apply (@H16 H11).
-------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H19.
--------------- intro H19.
apply (@H17).
----------------left.
exact H19.

--------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H20.
---------------- intro H20.
apply (@H17).
-----------------right.
exact H20.

---------------- contradiction H18.
------- destruct H11 as [H12|H12].
-------- assert (* Cut *) ((A = B) -> False) as H13.
--------- intro H13.
apply (@H7).
----------left.
exact H13.

--------- assert (* Cut *) (((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) -> False) as H14.
---------- intro H14.
apply (@H7).
-----------right.
exact H14.

---------- assert (* Cut *) ((B = C) -> False) as H15.
----------- intro H15.
apply (@H14).
------------left.
exact H15.

----------- assert (* Cut *) (((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) -> False) as H16.
------------ intro H16.
apply (@H14).
-------------right.
exact H16.

------------ assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H17.
------------- intro H17.
apply (@H16).
--------------left.
exact H17.

------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H18.
-------------- intro H18.
apply (@H16).
---------------right.
exact H18.

-------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H19.
--------------- intro H19.
apply (@H18).
----------------left.
exact H19.

--------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H20.
---------------- intro H20.
apply (@H18).
-----------------right.
exact H20.

---------------- assert (* Cut *) (False) as H21.
----------------- apply (@H19 H12).
----------------- contradiction H21.
-------- assert (* Cut *) ((A = B) -> False) as H13.
--------- intro H13.
apply (@H7).
----------left.
exact H13.

--------- assert (* Cut *) (((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) -> False) as H14.
---------- intro H14.
apply (@H7).
-----------right.
exact H14.

---------- assert (* Cut *) ((B = C) -> False) as H15.
----------- intro H15.
apply (@H14).
------------left.
exact H15.

----------- assert (* Cut *) (((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) -> False) as H16.
------------ intro H16.
apply (@H14).
-------------right.
exact H16.

------------ assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H17.
------------- intro H17.
apply (@H16).
--------------left.
exact H17.

------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H18.
-------------- intro H18.
apply (@H16).
---------------right.
exact H18.

-------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H19.
--------------- intro H19.
apply (@H18).
----------------left.
exact H19.

--------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H20.
---------------- intro H20.
apply (@H18).
-----------------right.
exact H20.

---------------- assert (* Cut *) (False) as H21.
----------------- apply (@H20 H12).
----------------- contradiction H21.

-- assert ((A = B) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))) as H8 by exact H7.
assert ((A = B) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))) as __TmpHyp by exact H8.
destruct __TmpHyp as [H9|H9].
--- assert (* Cut *) (euclidean__axioms.Cong B B a b) as H10.
---- apply (@eq__ind__r euclidean__axioms.Point B (fun A0 => (euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Cong A0 B a b) -> ((euclidean__axioms.Cong A0 D a d) -> ((euclidean__axioms.Cong A0 C a c) -> ((euclidean__axioms.neq A0 C) -> (((A0 = B) \/ ((A0 = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A0 C) \/ ((euclidean__axioms.BetS A0 B C) \/ (euclidean__axioms.BetS A0 C B)))))) -> (euclidean__axioms.Cong B B a b)))))))) with (x := A).
-----intro H10.
intro H11.
intro H12.
intro H13.
intro H14.
intro H15.
exact H11.

----- exact H9.
----- exact H.
----- exact H0.
----- exact H2.
----- exact H4.
----- exact H5.
----- exact H6.
---- assert (* Cut *) (euclidean__axioms.Cong a b B B) as H11.
----- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric a B B b H10).
----- assert (* Cut *) (~(euclidean__axioms.neq a b)) as H12.
------ intro H12.
assert (* Cut *) (euclidean__axioms.neq B B) as H13.
------- apply (@euclidean__axioms.axiom__nocollapse a b B B H12 H11).
------- assert (* Cut *) (B = B) as H14.
-------- apply (@logic.eq__refl Point B).
-------- apply (@H13 H14).
------ assert (* Cut *) (euclidean__axioms.Cong B D a d) as H13.
------- apply (@eq__ind__r euclidean__axioms.Point B (fun A0 => (euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Cong A0 B a b) -> ((euclidean__axioms.Cong A0 D a d) -> ((euclidean__axioms.Cong A0 C a c) -> ((euclidean__axioms.neq A0 C) -> (((A0 = B) \/ ((A0 = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A0 C) \/ ((euclidean__axioms.BetS A0 B C) \/ (euclidean__axioms.BetS A0 C B)))))) -> (euclidean__axioms.Cong B D a d)))))))) with (x := A).
--------intro H13.
intro H14.
intro H15.
intro H16.
intro H17.
intro H18.
exact H15.

-------- exact H9.
-------- exact H.
-------- exact H0.
-------- exact H2.
-------- exact H4.
-------- exact H5.
-------- exact H6.
------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H14.
-------- apply (@eq__ind euclidean__axioms.Point a (fun X => euclidean__axioms.Cong B D X d)) with (y := b).
--------- exact H13.
---------apply (@euclidean__tactics.NNPP (a = b) H12).

-------- exact H14.
--- destruct H9 as [H10|H10].
---- assert (* Cut *) (euclidean__axioms.Cong B B b c) as H11.
----- apply (@eq__ind__r euclidean__axioms.Point C (fun B0 => (euclidean__axioms.Col A B0 C) -> ((euclidean__axioms.Cong A B0 a b) -> ((euclidean__axioms.Cong B0 C b c) -> (((A = B0) \/ ((A = C) \/ ((B0 = C) \/ ((euclidean__axioms.BetS B0 A C) \/ ((euclidean__axioms.BetS A B0 C) \/ (euclidean__axioms.BetS A C B0)))))) -> (euclidean__axioms.Cong B0 B0 b c)))))) with (x := B).
------intro H11.
intro H12.
intro H13.
intro H14.
exact H13.

------ exact H10.
------ exact H.
------ exact H0.
------ exact H1.
------ exact H6.
----- assert (* Cut *) (euclidean__axioms.Cong b c B B) as H12.
------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric b B B c H11).
------ assert (* Cut *) (~(euclidean__axioms.neq b c)) as H13.
------- intro H13.
assert (* Cut *) (euclidean__axioms.neq B B) as H14.
-------- apply (@euclidean__axioms.axiom__nocollapse b c B B H13 H12).
-------- assert (* Cut *) (B = B) as H15.
--------- apply (@logic.eq__refl Point B).
--------- apply (@H14 H15).
------- assert (* Cut *) (euclidean__axioms.Cong B D c d) as H14.
-------- apply (@eq__ind__r euclidean__axioms.Point C (fun B0 => (euclidean__axioms.Col A B0 C) -> ((euclidean__axioms.Cong A B0 a b) -> ((euclidean__axioms.Cong B0 C b c) -> (((A = B0) \/ ((A = C) \/ ((B0 = C) \/ ((euclidean__axioms.BetS B0 A C) \/ ((euclidean__axioms.BetS A B0 C) \/ (euclidean__axioms.BetS A C B0)))))) -> ((euclidean__axioms.Cong B0 B0 b c) -> ((euclidean__axioms.Cong b c B0 B0) -> (euclidean__axioms.Cong B0 D c d)))))))) with (x := B).
---------intro H14.
intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
exact H3.

--------- exact H10.
--------- exact H.
--------- exact H0.
--------- exact H1.
--------- exact H6.
--------- exact H11.
--------- exact H12.
-------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H15.
--------- apply (@eq__ind__r euclidean__axioms.Point c (fun X => euclidean__axioms.Cong B D X d)) with (x := b).
---------- exact H14.
----------apply (@euclidean__tactics.NNPP (b = c) H13).

--------- exact H15.
---- destruct H10 as [H11|H11].
----- assert (* Cut *) (euclidean__axioms.BetS C A B) as H12.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry B A C H11).
------ assert (* Cut *) (euclidean__axioms.Cong C A c a) as H13.
------- assert (* Cut *) ((euclidean__axioms.Cong C A c a) /\ ((euclidean__axioms.Cong C A a c) /\ (euclidean__axioms.Cong A C c a))) as H13.
-------- apply (@lemma__congruenceflip.lemma__congruenceflip A C a c H4).
-------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__axioms.Cong C B c b) as H14.
-------- assert (* Cut *) ((euclidean__axioms.Cong C B c b) /\ ((euclidean__axioms.Cong C B b c) /\ (euclidean__axioms.Cong B C c b))) as H14.
--------- apply (@lemma__congruenceflip.lemma__congruenceflip B C b c H1).
--------- destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H15.
-------- assert (* Cut *) (euclidean__axioms.BetS c a b) as H15.
--------- apply (@lemma__betweennesspreserved.lemma__betweennesspreserved C A B c a b H13 H14 H0 H12).
--------- assert (* Cut *) (euclidean__axioms.Cong D B d b) as H16.
---------- apply (@euclidean__axioms.axiom__5__line C A B D c a b d H0 H3 H2 H12 H15 H13).
---------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H17.
----------- assert (* Cut *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H17.
------------ apply (@lemma__congruenceflip.lemma__congruenceflip D B d b H16).
------------ destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H18.
----------- exact H17.
----- destruct H11 as [H12|H12].
------ assert (* Cut *) (euclidean__axioms.BetS a b c) as H13.
------- apply (@lemma__betweennesspreserved.lemma__betweennesspreserved A B C a b c H0 H4 H1 H12).
------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H14.
-------- apply (@lemma__interior5.lemma__interior5 A B C D a b c d H12 H13 H0 H1 H2 H3).
-------- exact H14.
------ assert (* Cut *) (euclidean__axioms.Cong C B c b) as H13.
------- assert (* Cut *) ((euclidean__axioms.Cong C B c b) /\ ((euclidean__axioms.Cong C B b c) /\ (euclidean__axioms.Cong B C c b))) as H13.
-------- apply (@lemma__congruenceflip.lemma__congruenceflip B C b c H1).
-------- destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H14.
------- assert (* Cut *) (euclidean__axioms.BetS a c b) as H14.
-------- apply (@lemma__betweennesspreserved.lemma__betweennesspreserved A C B a c b H4 H0 H13 H12).
-------- assert (* Cut *) (euclidean__axioms.Cong D B d b) as H15.
--------- apply (@euclidean__axioms.axiom__5__line A C B D a c b d H13 H2 H3 H12 H14 H4).
--------- assert (* Cut *) (euclidean__axioms.Cong B D b d) as H16.
---------- assert (* Cut *) ((euclidean__axioms.Cong B D b d) /\ ((euclidean__axioms.Cong B D d b) /\ (euclidean__axioms.Cong D B b d))) as H16.
----------- apply (@lemma__congruenceflip.lemma__congruenceflip D B d b H15).
----------- destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H17.
---------- exact H16.
- exact H7.
Qed.
