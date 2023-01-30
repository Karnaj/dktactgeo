Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennesspreserved.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__doublereverse.
Require Export lemma__equalitysymmetric.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Definition lemma__lessthancongruence : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point), (euclidean__defs.Lt A B C D) -> ((euclidean__axioms.Cong C D E F) -> (euclidean__defs.Lt A B E F)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro H.
intro H0.
assert (* Cut *) (exists (G: euclidean__axioms.Point), (euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B)) as H1.
- exact H.
- assert (exists G: euclidean__axioms.Point, ((euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B))) as H2.
-- exact H1.
-- destruct H2 as [G H2].
assert (* AndElim *) ((euclidean__axioms.BetS C G D) /\ (euclidean__axioms.Cong C G A B)) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* Cut *) (euclidean__axioms.neq C D) as H5.
---- assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H5.
----- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (G) (D) H3).
----- assert (* AndElim *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
exact H9.
---- assert (* Cut *) (euclidean__axioms.neq E F) as H6.
----- apply (@euclidean__axioms.axiom__nocollapse (C) (D) (E) (F) (H5) H0).
----- assert (* Cut *) (~(F = E)) as H7.
------ intro H7.
assert (* Cut *) (E = F) as H8.
------- apply (@lemma__equalitysymmetric.lemma__equalitysymmetric (E) (F) H7).
------- apply (@H6 H8).
------ assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.BetS F E P) /\ (euclidean__axioms.Cong E P F E)) as H8.
------- apply (@lemma__extension.lemma__extension (F) (E) (F) (E) (H7) H7).
------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.BetS F E P) /\ (euclidean__axioms.Cong E P F E))) as H9.
-------- exact H8.
-------- destruct H9 as [P H9].
assert (* AndElim *) ((euclidean__axioms.BetS F E P) /\ (euclidean__axioms.Cong E P F E)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__axioms.BetS P E F) as H12.
---------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (E) (P) H10).
---------- assert (* Cut *) (euclidean__axioms.neq P E) as H13.
----------- assert (* Cut *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq P E) /\ (euclidean__axioms.neq P F))) as H13.
------------ apply (@lemma__betweennotequal.lemma__betweennotequal (P) (E) (F) H12).
------------ assert (* AndElim *) ((euclidean__axioms.neq E F) /\ ((euclidean__axioms.neq P E) /\ (euclidean__axioms.neq P F))) as H14.
------------- exact H13.
------------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq P E) /\ (euclidean__axioms.neq P F)) as H16.
-------------- exact H15.
-------------- destruct H16 as [H16 H17].
exact H16.
----------- assert (* Cut *) (euclidean__axioms.neq C G) as H14.
------------ assert (* Cut *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H14.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal (C) (G) (D) H3).
------------- assert (* AndElim *) ((euclidean__axioms.neq G D) /\ ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq C G) /\ (euclidean__axioms.neq C D)) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
exact H17.
------------ assert (* Cut *) (euclidean__axioms.neq A B) as H15.
------------- apply (@euclidean__axioms.axiom__nocollapse (C) (G) (A) (B) (H14) H4).
------------- assert (* Cut *) (exists (H16: euclidean__axioms.Point), (euclidean__axioms.BetS P E H16) /\ (euclidean__axioms.Cong E H16 A B)) as H16.
-------------- apply (@lemma__extension.lemma__extension (P) (E) (A) (B) (H13) H15).
-------------- assert (exists H17: euclidean__axioms.Point, ((euclidean__axioms.BetS P E H17) /\ (euclidean__axioms.Cong E H17 A B))) as H18.
--------------- exact H16.
--------------- destruct H18 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.BetS P E H17) /\ (euclidean__axioms.Cong E H17 A B)) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* Cut *) (~(D = C)) as H21.
----------------- intro H21.
assert (* Cut *) (euclidean__axioms.BetS C G C) as H22.
------------------ apply (@eq__ind__r euclidean__axioms.Point C (fun D0: euclidean__axioms.Point => (euclidean__defs.Lt A B C D0) -> ((euclidean__axioms.Cong C D0 E F) -> ((euclidean__axioms.BetS C G D0) -> ((euclidean__axioms.neq C D0) -> (euclidean__axioms.BetS C G C)))))) with (x := D).
-------------------intro H22.
intro H23.
intro H24.
intro H25.
exact H24.

------------------- exact H21.
------------------- exact H.
------------------- exact H0.
------------------- exact H3.
------------------- exact H5.
------------------ assert (* Cut *) (~(euclidean__axioms.BetS C G C)) as H23.
------------------- apply (@euclidean__axioms.axiom__betweennessidentity (C) G).
------------------- apply (@H23 H22).
----------------- assert (* Cut *) (euclidean__axioms.neq P E) as H22.
------------------ assert (* Cut *) ((euclidean__axioms.neq E H17) /\ ((euclidean__axioms.neq P E) /\ (euclidean__axioms.neq P H17))) as H22.
------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (E) (H17) H19).
------------------- assert (* AndElim *) ((euclidean__axioms.neq E H17) /\ ((euclidean__axioms.neq P E) /\ (euclidean__axioms.neq P H17))) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq P E) /\ (euclidean__axioms.neq P H17)) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
exact H25.
------------------ assert (* Cut *) (euclidean__axioms.neq E P) as H23.
------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (P) (E) H22).
------------------- assert (* Cut *) (exists (Q: euclidean__axioms.Point), (euclidean__axioms.BetS D C Q) /\ (euclidean__axioms.Cong C Q E P)) as H24.
-------------------- apply (@lemma__extension.lemma__extension (D) (C) (E) (P) (H21) H23).
-------------------- assert (exists Q: euclidean__axioms.Point, ((euclidean__axioms.BetS D C Q) /\ (euclidean__axioms.Cong C Q E P))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [Q H25].
assert (* AndElim *) ((euclidean__axioms.BetS D C Q) /\ (euclidean__axioms.Cong C Q E P)) as H26.
---------------------- exact H25.
---------------------- destruct H26 as [H26 H27].
assert (* Cut *) (euclidean__axioms.BetS Q C D) as H28.
----------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (D) (C) (Q) H26).
----------------------- assert (* Cut *) (euclidean__axioms.Cong Q C C Q) as H29.
------------------------ apply (@euclidean__axioms.cn__equalityreverse (Q) C).
------------------------ assert (* Cut *) (euclidean__axioms.Cong Q C E P) as H30.
------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (Q) (C) (C) (Q) (E) (P) (H29) H27).
------------------------- assert (* Cut *) (euclidean__axioms.Cong E P P E) as H31.
-------------------------- apply (@euclidean__axioms.cn__equalityreverse (E) P).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong Q C P E) as H32.
--------------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (Q) (C) (E) (P) (P) (E) (H30) H31).
--------------------------- assert (* Cut *) (euclidean__axioms.Cong Q D P F) as H33.
---------------------------- apply (@euclidean__axioms.cn__sumofparts (Q) (C) (D) (P) (E) (F) (H32) (H0) (H28) H12).
---------------------------- assert (* Cut *) (euclidean__axioms.Cong A B E H17) as H34.
----------------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (A) (E) (H17) (B) H20).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong C G E H17) as H35.
------------------------------ apply (@lemma__congruencetransitive.lemma__congruencetransitive (C) (G) (A) (B) (E) (H17) (H4) H34).
------------------------------ assert (* Cut *) (euclidean__axioms.BetS Q C G) as H36.
------------------------------- apply (@euclidean__axioms.axiom__innertransitivity (Q) (C) (G) (D) (H28) H3).
------------------------------- assert (* Cut *) (euclidean__axioms.Cong D G F H17) as H37.
-------------------------------- apply (@euclidean__axioms.axiom__5__line (Q) (C) (G) (D) (P) (E) (H17) (F) (H35) (H33) (H0) (H36) (H19) H32).
-------------------------------- assert (* Cut *) (euclidean__axioms.Cong G D H17 F) as H38.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Cong H17 F G D) /\ (euclidean__axioms.Cong G D H17 F)) as H38.
---------------------------------- apply (@lemma__doublereverse.lemma__doublereverse (D) (G) (F) (H17) H37).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Cong H17 F G D) /\ (euclidean__axioms.Cong G D H17 F)) as H39.
----------------------------------- exact H38.
----------------------------------- destruct H39 as [H39 H40].
exact H40.
--------------------------------- assert (* Cut *) (euclidean__axioms.BetS E H17 F) as H39.
---------------------------------- apply (@lemma__betweennesspreserved.lemma__betweennesspreserved (C) (G) (D) (E) (H17) (F) (H35) (H0) (H38) H3).
---------------------------------- assert (* Cut *) (euclidean__defs.Lt A B E F) as H40.
----------------------------------- exists H17.
split.
------------------------------------ exact H39.
------------------------------------ exact H20.
----------------------------------- exact H40.
Qed.
