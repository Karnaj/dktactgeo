Require Export euclidean__axioms.
Require Export lemma__betweennesspreserved.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export logic.
Definition lemma__collinearitypreserved : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Col A B C) -> ((euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong A C a c) -> ((euclidean__axioms.Cong B C b c) -> (euclidean__axioms.Col a b c)))).
Proof.
intro A.
intro B.
intro C.
intro a.
intro b.
intro c.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.Cong C B B C) as H3.
- apply (@euclidean__axioms.cn__equalityreverse (C) B).
- assert (* Cut *) (euclidean__axioms.Cong C B b c) as H4.
-- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (B) (B) (C) (b) (c) (H3) H2).
-- assert (* Cut *) (euclidean__axioms.Cong b c c b) as H5.
--- apply (@euclidean__axioms.cn__equalityreverse (b) c).
--- assert (* Cut *) (euclidean__axioms.Cong C B c b) as H6.
---- apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (B) (b) (c) (c) (b) (H4) H5).
---- assert (* Cut *) (euclidean__axioms.Cong a b b a) as H7.
----- apply (@euclidean__axioms.cn__equalityreverse (a) b).
----- assert (* Cut *) (euclidean__axioms.Cong A B b a) as H8.
------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (B) (a) (b) (b) (a) (H0) H7).
------ assert (* Cut *) (euclidean__axioms.Cong A B B A) as H9.
------- apply (@euclidean__axioms.cn__equalityreverse (A) B).
------- assert (* Cut *) (euclidean__axioms.Cong B A A B) as H10.
-------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (A) (B) (A) H9).
-------- assert (* Cut *) (euclidean__axioms.Cong B A b a) as H11.
--------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (A) (A) (B) (b) (a) (H10) H8).
--------- assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H12.
---------- exact H.
---------- assert (* Cut *) (euclidean__axioms.Col a b c) as H13.
----------- assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H13.
------------ exact H12.
------------ assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as __TmpHyp.
------------- exact H13.
------------- assert (A = B \/ (A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))) as H14.
-------------- exact __TmpHyp.
-------------- destruct H14 as [H14|H14].
--------------- assert (* Cut *) (euclidean__axioms.Cong A A a b) as H15.
---------------- apply (@eq__ind__r euclidean__axioms.Point B (fun A0: euclidean__axioms.Point => (euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Cong A0 B a b) -> ((euclidean__axioms.Cong A0 C a c) -> ((euclidean__axioms.Cong A0 B b a) -> ((euclidean__axioms.Cong A0 B B A0) -> ((euclidean__axioms.Cong B A0 A0 B) -> ((euclidean__axioms.Cong B A0 b a) -> (euclidean__axioms.Cong A0 A0 a b))))))))) with (x := A).
-----------------intro H15.
intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
exact H16.

----------------- exact H14.
----------------- exact H.
----------------- exact H0.
----------------- exact H1.
----------------- exact H8.
----------------- exact H9.
----------------- exact H10.
----------------- exact H11.
---------------- assert (* Cut *) (euclidean__axioms.Cong a b A A) as H16.
----------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (A) (A) (b) H15).
----------------- assert (* Cut *) (~(euclidean__axioms.neq a b)) as H17.
------------------ intro H17.
assert (* Cut *) (euclidean__axioms.neq A A) as H18.
------------------- apply (@euclidean__axioms.axiom__nocollapse (a) (b) (A) (A) (H17) H16).
------------------- assert (* Cut *) (A = A) as H19.
-------------------- assert (* Cut *) (False) as H19.
--------------------- assert (* Cut *) (A = A) as H19.
---------------------- apply (@logic.eq__refl (Point) A).
---------------------- apply (@H18 H19).
--------------------- assert (* Cut *) (False) as H20.
---------------------- exact H19.
---------------------- apply (@logic.eq__refl (Point) A).
-------------------- apply (@H18 H19).
------------------ assert (* Cut *) (a = b) as H18.
------------------- apply (@euclidean__axioms.cn__stability (a) (b) H17).
------------------- assert (* Cut *) (euclidean__axioms.Col a b c) as H19.
-------------------- left.
exact H18.
-------------------- exact H19.
--------------- assert (A = C \/ (B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))) as H15.
---------------- exact H14.
---------------- destruct H15 as [H15|H15].
----------------- assert (* Cut *) (euclidean__axioms.Cong A A a c) as H16.
------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun A0: euclidean__axioms.Point => (euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Cong A0 B a b) -> ((euclidean__axioms.Cong A0 C a c) -> ((euclidean__axioms.Cong A0 B b a) -> ((euclidean__axioms.Cong A0 B B A0) -> ((euclidean__axioms.Cong B A0 A0 B) -> ((euclidean__axioms.Cong B A0 b a) -> (euclidean__axioms.Cong A0 A0 a c))))))))) with (x := A).
-------------------intro H16.
intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
exact H18.

------------------- exact H15.
------------------- exact H.
------------------- exact H0.
------------------- exact H1.
------------------- exact H8.
------------------- exact H9.
------------------- exact H10.
------------------- exact H11.
------------------ assert (* Cut *) (euclidean__axioms.Cong a c A A) as H17.
------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (A) (A) (c) H16).
------------------- assert (* Cut *) (~(euclidean__axioms.neq a c)) as H18.
-------------------- intro H18.
assert (* Cut *) (euclidean__axioms.neq A A) as H19.
--------------------- apply (@euclidean__axioms.axiom__nocollapse (a) (c) (A) (A) (H18) H17).
--------------------- assert (* Cut *) (A = A) as H20.
---------------------- assert (* Cut *) (False) as H20.
----------------------- assert (* Cut *) (A = A) as H20.
------------------------ apply (@logic.eq__refl (Point) A).
------------------------ apply (@H19 H20).
----------------------- assert (* Cut *) (False) as H21.
------------------------ exact H20.
------------------------ apply (@logic.eq__refl (Point) A).
---------------------- apply (@H19 H20).
-------------------- assert (* Cut *) (a = c) as H19.
--------------------- apply (@euclidean__axioms.cn__stability (a) (c) H18).
--------------------- assert (* Cut *) (euclidean__axioms.Col a b c) as H20.
---------------------- right.
left.
exact H19.
---------------------- exact H20.
----------------- assert (B = C \/ (euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) as H16.
------------------ exact H15.
------------------ destruct H16 as [H16|H16].
------------------- assert (* Cut *) (euclidean__axioms.Cong B B b c) as H17.
-------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun B0: euclidean__axioms.Point => (euclidean__axioms.Col A B0 C) -> ((euclidean__axioms.Cong A B0 a b) -> ((euclidean__axioms.Cong B0 C b c) -> ((euclidean__axioms.Cong C B0 B0 C) -> ((euclidean__axioms.Cong C B0 b c) -> ((euclidean__axioms.Cong C B0 c b) -> ((euclidean__axioms.Cong A B0 b a) -> ((euclidean__axioms.Cong A B0 B0 A) -> ((euclidean__axioms.Cong B0 A A B0) -> ((euclidean__axioms.Cong B0 A b a) -> (euclidean__axioms.Cong B0 B0 b c)))))))))))) with (x := B).
---------------------intro H17.
intro H18.
intro H19.
intro H20.
intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
exact H19.

--------------------- exact H16.
--------------------- exact H.
--------------------- exact H0.
--------------------- exact H2.
--------------------- exact H3.
--------------------- exact H4.
--------------------- exact H6.
--------------------- exact H8.
--------------------- exact H9.
--------------------- exact H10.
--------------------- exact H11.
-------------------- assert (* Cut *) (euclidean__axioms.Cong b c B B) as H18.
--------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (b) (B) (B) (c) H17).
--------------------- assert (* Cut *) (~(euclidean__axioms.neq b c)) as H19.
---------------------- intro H19.
assert (* Cut *) (euclidean__axioms.neq B B) as H20.
----------------------- apply (@euclidean__axioms.axiom__nocollapse (b) (c) (B) (B) (H19) H18).
----------------------- assert (* Cut *) (B = B) as H21.
------------------------ assert (* Cut *) (False) as H21.
------------------------- assert (* Cut *) (B = B) as H21.
-------------------------- apply (@logic.eq__refl (Point) B).
-------------------------- apply (@H20 H21).
------------------------- assert (* Cut *) (False) as H22.
-------------------------- exact H21.
-------------------------- apply (@logic.eq__refl (Point) B).
------------------------ apply (@H20 H21).
---------------------- assert (* Cut *) (b = c) as H20.
----------------------- apply (@euclidean__axioms.cn__stability (b) (c) H19).
----------------------- assert (* Cut *) (euclidean__axioms.Col a b c) as H21.
------------------------ right.
right.
left.
exact H20.
------------------------ exact H21.
------------------- assert (euclidean__axioms.BetS B A C \/ (euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) as H17.
-------------------- exact H16.
-------------------- destruct H17 as [H17|H17].
--------------------- assert (* Cut *) (euclidean__axioms.BetS b a c) as H18.
---------------------- apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (B) (A) (C) (b) (a) (c) (H11) (H2) (H1) H17).
---------------------- assert (* Cut *) (euclidean__axioms.Col a b c) as H19.
----------------------- right.
right.
right.
left.
exact H18.
----------------------- exact H19.
--------------------- assert (euclidean__axioms.BetS A B C \/ euclidean__axioms.BetS A C B) as H18.
---------------------- exact H17.
---------------------- destruct H18 as [H18|H18].
----------------------- assert (* Cut *) (euclidean__axioms.BetS a b c) as H19.
------------------------ apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (A) (B) (C) (a) (b) (c) (H0) (H1) (H2) H18).
------------------------ assert (* Cut *) (euclidean__axioms.Col a b c) as H20.
------------------------- right.
right.
right.
right.
left.
exact H19.
------------------------- exact H20.
----------------------- assert (* Cut *) (euclidean__axioms.BetS a c b) as H19.
------------------------ apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (A) (C) (B) (a) (c) (b) (H1) (H0) (H6) H18).
------------------------ assert (* Cut *) (euclidean__axioms.Col a b c) as H20.
------------------------- right.
right.
right.
right.
right.
exact H19.
------------------------- exact H20.
----------- exact H13.
Qed.
