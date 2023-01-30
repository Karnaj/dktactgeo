Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__inequalitysymmetric.
Require Export lemma__localextension.
Require Export logic.
Definition lemma__differenceofparts : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point), (euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong A C a c) -> ((euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS a b c) -> (euclidean__axioms.Cong B C b c)))).
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
assert (* Cut *) (euclidean__axioms.Cong B C b c) as H3.
- assert (* Cut *) ((B = A) \/ (euclidean__axioms.neq B A)) as H3.
-- apply (@euclidean__tactics.eq__or__neq (B) A).
-- assert (* Cut *) ((B = A) \/ (euclidean__axioms.neq B A)) as H4.
--- exact H3.
--- assert (* Cut *) ((B = A) \/ (euclidean__axioms.neq B A)) as __TmpHyp.
---- exact H4.
---- assert (B = A \/ euclidean__axioms.neq B A) as H5.
----- exact __TmpHyp.
----- destruct H5 as [H5|H5].
------ assert (* Cut *) (euclidean__axioms.Cong A A a b) as H6.
------- apply (@eq__ind__r euclidean__axioms.Point A (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__axioms.BetS A B0 C) -> (euclidean__axioms.Cong A A a b)))) with (x := B).
--------intro H6.
intro H7.
exact H6.

-------- exact H5.
-------- exact H.
-------- exact H1.
------- assert (* Cut *) (euclidean__axioms.Cong a b A A) as H7.
-------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (A) (A) (b) H6).
-------- assert (* Cut *) (~(euclidean__axioms.neq a b)) as H8.
--------- intro H8.
assert (* Cut *) (euclidean__axioms.neq A A) as H9.
---------- apply (@euclidean__axioms.axiom__nocollapse (a) (b) (A) (A) (H8) H7).
---------- assert (* Cut *) (A = A) as H10.
----------- assert (* Cut *) (False) as H10.
------------ assert (* Cut *) (A = A) as H10.
------------- apply (@logic.eq__refl (Point) A).
------------- apply (@H9 H10).
------------ assert (* Cut *) (False) as H11.
------------- exact H10.
------------- apply (@logic.eq__refl (Point) A).
----------- apply (@H9 H10).
--------- assert (* Cut *) (euclidean__axioms.Cong A C A C) as H9.
---------- apply (@euclidean__axioms.cn__congruencereflexive (A) C).
---------- assert (* Cut *) (euclidean__axioms.Cong B C A C) as H10.
----------- apply (@eq__ind__r euclidean__axioms.Point A (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__axioms.BetS A B0 C) -> (euclidean__axioms.Cong B0 C A C)))) with (x := B).
------------intro H10.
intro H11.
exact H9.

------------ exact H5.
------------ exact H.
------------ exact H1.
----------- assert (* Cut *) (euclidean__axioms.Cong B C a c) as H11.
------------ apply (@eq__ind__r euclidean__axioms.Point A (fun B0: euclidean__axioms.Point => (euclidean__axioms.Cong A B0 a b) -> ((euclidean__axioms.BetS A B0 C) -> ((euclidean__axioms.Cong B0 C A C) -> (euclidean__axioms.Cong B0 C a c))))) with (x := B).
-------------intro H11.
intro H12.
intro H13.
exact H0.

------------- exact H5.
------------- exact H.
------------- exact H1.
------------- exact H10.
------------ assert (* Cut *) (euclidean__axioms.Cong b c b c) as H12.
------------- apply (@euclidean__axioms.cn__congruencereflexive (b) c).
------------- assert (* Cut *) (euclidean__axioms.Cong b c a c) as H13.
-------------- apply (@eq__ind__r euclidean__axioms.Point b (fun X: euclidean__axioms.Point => euclidean__axioms.Cong b c X c)) with (x := a).
--------------- exact H12.
---------------apply (@euclidean__tactics.NNPP (a = b) H8).

-------------- assert (* Cut *) (euclidean__axioms.Cong a c b c) as H14.
--------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (b) (c) (c) H13).
--------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H15.
---------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (B) (C) (a) (c) (b) (c) (H11) H14).
---------------- exact H15.
------ assert (* Cut *) (~(C = A)) as H6.
------- intro H6.
assert (* Cut *) (euclidean__axioms.BetS A B A) as H7.
-------- apply (@eq__ind__r euclidean__axioms.Point A (fun C0: euclidean__axioms.Point => (euclidean__axioms.Cong A C0 a c) -> ((euclidean__axioms.BetS A B C0) -> (euclidean__axioms.BetS A B A)))) with (x := C).
---------intro H7.
intro H8.
exact H8.

--------- exact H6.
--------- exact H0.
--------- exact H1.
-------- assert (* Cut *) (~(euclidean__axioms.BetS A B A)) as H8.
--------- apply (@euclidean__axioms.axiom__betweennessidentity (A) B).
--------- apply (@H8 H7).
------- assert (* Cut *) (euclidean__axioms.neq A C) as H7.
-------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (A) H6).
-------- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS C A E) /\ (euclidean__axioms.Cong A E A C)) as H8.
--------- apply (@lemma__localextension.lemma__localextension (C) (A) (C) (H6) H7).
--------- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS C A E) /\ (euclidean__axioms.Cong A E A C))) as H9.
---------- exact H8.
---------- destruct H9 as [E H9].
assert (* AndElim *) ((euclidean__axioms.BetS C A E) /\ (euclidean__axioms.Cong A E A C)) as H10.
----------- exact H9.
----------- destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__axioms.neq A C) as H12.
------------ exact H7.
------------ assert (* Cut *) (euclidean__axioms.neq a c) as H13.
------------- apply (@euclidean__axioms.axiom__nocollapse (A) (C) (a) (c) (H12) H0).
------------- assert (* Cut *) (euclidean__axioms.neq c a) as H14.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (a) (c) H13).
-------------- assert (* Cut *) (exists (e: euclidean__axioms.Point), (euclidean__axioms.BetS c a e) /\ (euclidean__axioms.Cong a e a c)) as H15.
--------------- apply (@lemma__localextension.lemma__localextension (c) (a) (c) (H14) H13).
--------------- assert (exists e: euclidean__axioms.Point, ((euclidean__axioms.BetS c a e) /\ (euclidean__axioms.Cong a e a c))) as H16.
---------------- exact H15.
---------------- destruct H16 as [e H16].
assert (* AndElim *) ((euclidean__axioms.BetS c a e) /\ (euclidean__axioms.Cong a e a c)) as H17.
----------------- exact H16.
----------------- destruct H17 as [H17 H18].
assert (* Cut *) (euclidean__axioms.Cong E A A E) as H19.
------------------ apply (@euclidean__axioms.cn__equalityreverse (E) A).
------------------ assert (* Cut *) (euclidean__axioms.Cong E A A C) as H20.
------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (E) (A) (A) (E) (A) (C) (H19) H11).
------------------- assert (* Cut *) (euclidean__axioms.Cong E A a c) as H21.
-------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (E) (A) (A) (C) (a) (c) (H20) H0).
-------------------- assert (* Cut *) (euclidean__axioms.Cong e a a e) as H22.
--------------------- apply (@euclidean__axioms.cn__equalityreverse (e) a).
--------------------- assert (* Cut *) (euclidean__axioms.Cong e a a c) as H23.
---------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (e) (a) (a) (e) (a) (c) (H22) H18).
---------------------- assert (* Cut *) (euclidean__axioms.Cong a c e a) as H24.
----------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (a) (e) (a) (c) H23).
----------------------- assert (* Cut *) (euclidean__axioms.Cong E A a c) as H25.
------------------------ exact H21.
------------------------ assert (* Cut *) (euclidean__axioms.Cong E A e a) as H26.
------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (E) (A) (a) (c) (e) (a) (H25) H24).
------------------------- assert (* Cut *) (euclidean__axioms.BetS E A C) as H27.
-------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (A) (E) H10).
-------------------------- assert (* Cut *) (euclidean__axioms.BetS e a c) as H28.
--------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (c) (a) (e) H17).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong E C e c) as H29.
---------------------------- apply (@euclidean__axioms.cn__sumofparts (E) (A) (C) (e) (a) (c) (H26) (H0) (H27) H28).
---------------------------- assert (* Cut *) (euclidean__axioms.BetS E A B) as H30.
----------------------------- apply (@euclidean__axioms.axiom__innertransitivity (E) (A) (B) (C) (H27) H1).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS e a b) as H31.
------------------------------ apply (@euclidean__axioms.axiom__innertransitivity (e) (a) (b) (c) (H28) H2).
------------------------------ assert (* Cut *) (euclidean__axioms.Cong C B c b) as H32.
------------------------------- apply (@euclidean__axioms.axiom__5__line (E) (A) (B) (C) (e) (a) (b) (c) (H) (H29) (H0) (H30) (H31) H26).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong b c B C) as H33.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Cong b c B C) /\ (euclidean__axioms.Cong B C b c)) as H33.
--------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (C) (B) (c) (b) H32).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong b c B C) /\ (euclidean__axioms.Cong B C b c)) as H34.
---------------------------------- exact H33.
---------------------------------- destruct H34 as [H34 H35].
exact H34.
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong B C b c) as H34.
--------------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (B) (b) (c) (C) H33).
--------------------------------- exact H34.
- exact H3.
Qed.
