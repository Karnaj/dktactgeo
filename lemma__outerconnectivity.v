Require Export euclidean__axioms.
Require Export lemma__3__5b.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__differenceofparts.
Require Export lemma__extension.
Require Export lemma__extensionunique.
Require Export logic.
Definition lemma__outerconnectivity : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS A B D) -> ((~(euclidean__axioms.BetS B C D)) -> ((~(euclidean__axioms.BetS B D C)) -> (C = D)))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (~(A = C)) as H3.
- intro H3.
assert (* Cut *) (euclidean__axioms.BetS A B A) as H4.
-- apply (@eq__ind__r euclidean__axioms.Point C (fun A0: euclidean__axioms.Point => (euclidean__axioms.BetS A0 B C) -> ((euclidean__axioms.BetS A0 B D) -> (euclidean__axioms.BetS A0 B A0)))) with (x := A).
---intro H4.
intro H5.
exact H4.

--- exact H3.
--- exact H.
--- exact H0.
-- assert (* Cut *) (~(euclidean__axioms.BetS A B A)) as H5.
--- apply (@euclidean__axioms.axiom__betweennessidentity (A) B).
--- apply (@H5 H4).
- assert (* Cut *) (euclidean__axioms.neq A D) as H4.
-- assert (* Cut *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H4.
--- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (D) H0).
--- assert (* AndElim *) ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A D)) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
exact H8.
-- assert (* Cut *) (exists (E: euclidean__axioms.Point), (euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E A D)) as H5.
--- apply (@lemma__extension.lemma__extension (A) (C) (A) (D) (H3) H4).
--- assert (exists E: euclidean__axioms.Point, ((euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E A D))) as H6.
---- exact H5.
---- destruct H6 as [E H6].
assert (* AndElim *) ((euclidean__axioms.BetS A C E) /\ (euclidean__axioms.Cong C E A D)) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* Cut *) (euclidean__axioms.BetS A B E) as H9.
------ apply (@lemma__3__6b.lemma__3__6b (A) (B) (C) (E) (H) H7).
------ assert (* Cut *) (~(A = D)) as H10.
------- intro H10.
assert (* Cut *) (euclidean__axioms.BetS A B A) as H11.
-------- apply (@eq__ind__r euclidean__axioms.Point D (fun A0: euclidean__axioms.Point => (euclidean__axioms.BetS A0 B C) -> ((euclidean__axioms.BetS A0 B D) -> ((~(A0 = C)) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.BetS A0 C E) -> ((euclidean__axioms.Cong C E A0 D) -> ((euclidean__axioms.BetS A0 B E) -> (euclidean__axioms.BetS A0 B A0))))))))) with (x := A).
---------intro H11.
intro H12.
intro H13.
intro H14.
intro H15.
intro H16.
intro H17.
exact H12.

--------- exact H10.
--------- exact H.
--------- exact H0.
--------- exact H3.
--------- exact H4.
--------- exact H7.
--------- exact H8.
--------- exact H9.
-------- assert (* Cut *) (~(euclidean__axioms.BetS A B A)) as H12.
--------- apply (@euclidean__axioms.axiom__betweennessidentity (A) B).
--------- apply (@H4 H10).
------- assert (* Cut *) (euclidean__axioms.neq A C) as H11.
-------- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H11.
--------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (E) H9).
--------- assert (* AndElim *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A E)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
exact H3.
-------- assert (* Cut *) (exists (F: euclidean__axioms.Point), (euclidean__axioms.BetS A D F) /\ (euclidean__axioms.Cong D F A C)) as H12.
--------- apply (@lemma__extension.lemma__extension (A) (D) (A) (C) (H10) H11).
--------- assert (exists F: euclidean__axioms.Point, ((euclidean__axioms.BetS A D F) /\ (euclidean__axioms.Cong D F A C))) as H13.
---------- exact H12.
---------- destruct H13 as [F H13].
assert (* AndElim *) ((euclidean__axioms.BetS A D F) /\ (euclidean__axioms.Cong D F A C)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* Cut *) (euclidean__axioms.BetS F D A) as H16.
------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (D) (F) H14).
------------ assert (* Cut *) (euclidean__axioms.BetS D B A) as H17.
------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (D) H0).
------------- assert (* Cut *) (euclidean__axioms.BetS F B A) as H18.
-------------- apply (@lemma__3__5b.lemma__3__5b (F) (D) (B) (A) (H16) H17).
-------------- assert (* Cut *) (euclidean__axioms.BetS A B F) as H19.
--------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (B) (A) H18).
--------------- assert (* Cut *) (euclidean__axioms.Cong F D D F) as H20.
---------------- apply (@euclidean__axioms.cn__equalityreverse (F) D).
---------------- assert (* Cut *) (euclidean__axioms.Cong F D A C) as H21.
----------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (D) (D) (F) (A) (C) (H20) H15).
----------------- assert (* Cut *) (euclidean__axioms.Cong A D C E) as H22.
------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (C) (E) (D) H8).
------------------ assert (* Cut *) (euclidean__axioms.Cong D A A D) as H23.
------------------- apply (@euclidean__axioms.cn__equalityreverse (D) A).
------------------- assert (* Cut *) (euclidean__axioms.Cong D A C E) as H24.
-------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (D) (A) (A) (D) (C) (E) (H23) H22).
-------------------- assert (* Cut *) (euclidean__axioms.Cong F A A E) as H25.
--------------------- apply (@euclidean__axioms.cn__sumofparts (F) (D) (A) (A) (C) (E) (H21) (H24) (H16) H7).
--------------------- assert (* Cut *) (euclidean__axioms.Cong A E F A) as H26.
---------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (F) (A) (E) H25).
---------------------- assert (* Cut *) (euclidean__axioms.Cong F A A F) as H27.
----------------------- apply (@euclidean__axioms.cn__equalityreverse (F) A).
----------------------- assert (* Cut *) (euclidean__axioms.Cong A E A F) as H28.
------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (A) (E) (F) (A) (A) (F) (H26) H27).
------------------------ assert (* Cut *) (euclidean__axioms.Cong A B A B) as H29.
------------------------- apply (@euclidean__axioms.cn__congruencereflexive (A) B).
------------------------- assert (* Cut *) (euclidean__axioms.Cong B E B F) as H30.
-------------------------- apply (@lemma__differenceofparts.lemma__differenceofparts (A) (B) (E) (A) (B) (F) (H29) (H28) (H9) H19).
-------------------------- assert (* Cut *) (E = F) as H31.
--------------------------- apply (@lemma__extensionunique.lemma__extensionunique (A) (B) (E) (F) (H9) (H19) H30).
--------------------------- assert (* Cut *) (euclidean__axioms.BetS A D E) as H32.
---------------------------- apply (@eq__ind__r euclidean__axioms.Point F (fun E0: euclidean__axioms.Point => (euclidean__axioms.BetS A C E0) -> ((euclidean__axioms.Cong C E0 A D) -> ((euclidean__axioms.BetS A B E0) -> ((euclidean__axioms.Cong A D C E0) -> ((euclidean__axioms.Cong D A C E0) -> ((euclidean__axioms.Cong F A A E0) -> ((euclidean__axioms.Cong A E0 F A) -> ((euclidean__axioms.Cong A E0 A F) -> ((euclidean__axioms.Cong B E0 B F) -> (euclidean__axioms.BetS A D E0))))))))))) with (x := E).
-----------------------------intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
exact H14.

----------------------------- exact H31.
----------------------------- exact H7.
----------------------------- exact H8.
----------------------------- exact H9.
----------------------------- exact H22.
----------------------------- exact H24.
----------------------------- exact H25.
----------------------------- exact H26.
----------------------------- exact H28.
----------------------------- exact H30.
---------------------------- assert (* Cut *) (euclidean__axioms.BetS B C E) as H33.
----------------------------- apply (@lemma__3__6a.lemma__3__6a (A) (B) (C) (E) (H) H7).
----------------------------- assert (* Cut *) (euclidean__axioms.BetS B D E) as H34.
------------------------------ apply (@lemma__3__6a.lemma__3__6a (A) (B) (D) (E) (H0) H32).
------------------------------ assert (* Cut *) (C = D) as H35.
------------------------------- apply (@euclidean__axioms.axiom__connectivity (B) (C) (D) (E) (H33) (H34) (H1) H2).
------------------------------- exact H35.
Qed.
