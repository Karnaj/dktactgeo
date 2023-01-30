Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__layoffunique.
Require Export lemma__lessthantransitive.
Require Export lemma__ray4.
Require Export logic.
Definition lemma__TTtransitive : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point) (S: euclidean__axioms.Point), (euclidean__defs.TT A B C D E F G H) -> ((euclidean__defs.TT E F G H P Q R S) -> (euclidean__defs.TT A B C D P Q R S)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro P.
intro Q.
intro R.
intro S.
intro H0.
intro H1.
assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.BetS E F K) /\ ((euclidean__axioms.Cong F K G H) /\ (euclidean__defs.TG A B C D E K))) as H2.
- exact H0.
- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.BetS E F K) /\ ((euclidean__axioms.Cong F K G H) /\ (euclidean__defs.TG A B C D E K)))) as H3.
-- exact H2.
-- destruct H3 as [K H3].
assert (* AndElim *) ((euclidean__axioms.BetS E F K) /\ ((euclidean__axioms.Cong F K G H) /\ (euclidean__defs.TG A B C D E K))) as H4.
--- exact H3.
--- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__axioms.Cong F K G H) /\ (euclidean__defs.TG A B C D E K)) as H6.
---- exact H5.
---- destruct H6 as [H6 H7].
assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS A B J) /\ ((euclidean__axioms.Cong B J C D) /\ (euclidean__defs.Lt E K A J))) as H8.
----- exact H7.
----- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS A B J) /\ ((euclidean__axioms.Cong B J C D) /\ (euclidean__defs.Lt E K A J)))) as H9.
------ exact H8.
------ destruct H9 as [J H9].
assert (* AndElim *) ((euclidean__axioms.BetS A B J) /\ ((euclidean__axioms.Cong B J C D) /\ (euclidean__defs.Lt E K A J))) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Cong B J C D) /\ (euclidean__defs.Lt E K A J)) as H12.
-------- exact H11.
-------- destruct H12 as [H12 H13].
assert (* Cut *) (exists (L: euclidean__axioms.Point), (euclidean__axioms.BetS P Q L) /\ ((euclidean__axioms.Cong Q L R S) /\ (euclidean__defs.TG E F G H P L))) as H14.
--------- exact H1.
--------- assert (exists L: euclidean__axioms.Point, ((euclidean__axioms.BetS P Q L) /\ ((euclidean__axioms.Cong Q L R S) /\ (euclidean__defs.TG E F G H P L)))) as H15.
---------- exact H14.
---------- destruct H15 as [L H15].
assert (* AndElim *) ((euclidean__axioms.BetS P Q L) /\ ((euclidean__axioms.Cong Q L R S) /\ (euclidean__defs.TG E F G H P L))) as H16.
----------- exact H15.
----------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Cong Q L R S) /\ (euclidean__defs.TG E F G H P L)) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS E F M) /\ ((euclidean__axioms.Cong F M G H) /\ (euclidean__defs.Lt P L E M))) as H20.
------------- exact H19.
------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS E F M) /\ ((euclidean__axioms.Cong F M G H) /\ (euclidean__defs.Lt P L E M)))) as H21.
-------------- exact H20.
-------------- destruct H21 as [M H21].
assert (* AndElim *) ((euclidean__axioms.BetS E F M) /\ ((euclidean__axioms.Cong F M G H) /\ (euclidean__defs.Lt P L E M))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.Cong F M G H) /\ (euclidean__defs.Lt P L E M)) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
assert (* Cut *) (K = K) as H26.
----------------- apply (@logic.eq__refl (Point) K).
----------------- assert (* Cut *) (euclidean__axioms.neq F K) as H27.
------------------ assert (* Cut *) ((euclidean__axioms.neq F K) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E K))) as H27.
------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (F) (K) H4).
------------------- assert (* AndElim *) ((euclidean__axioms.neq F K) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E K))) as H28.
-------------------- exact H27.
-------------------- destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E K)) as H30.
--------------------- exact H29.
--------------------- destruct H30 as [H30 H31].
exact H28.
------------------ assert (* Cut *) (euclidean__axioms.neq F M) as H28.
------------------- assert (* Cut *) ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E M))) as H28.
-------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (F) (M) H22).
-------------------- assert (* AndElim *) ((euclidean__axioms.neq F M) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E M))) as H29.
--------------------- exact H28.
--------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E M)) as H31.
---------------------- exact H30.
---------------------- destruct H31 as [H31 H32].
exact H29.
------------------- assert (* Cut *) (euclidean__defs.Out F K M) as H29.
-------------------- exists E.
split.
--------------------- exact H22.
--------------------- exact H4.
-------------------- assert (* Cut *) (euclidean__defs.Out F K K) as H30.
--------------------- apply (@lemma__ray4.lemma__ray4 (F) (K) (K)).
----------------------right.
left.
exact H26.

---------------------- exact H27.
--------------------- assert (* Cut *) (euclidean__axioms.Cong G H F M) as H31.
---------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (G) (F) (M) (H) H24).
---------------------- assert (* Cut *) (euclidean__axioms.Cong F K F M) as H32.
----------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (F) (K) (G) (H) (F) (M) (H6) H31).
----------------------- assert (* Cut *) (K = M) as H33.
------------------------ apply (@lemma__layoffunique.lemma__layoffunique (F) (K) (K) (M) (H30) (H29) H32).
------------------------ assert (* Cut *) (euclidean__defs.Lt P L E K) as H34.
------------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun K0: euclidean__axioms.Point => (euclidean__axioms.BetS E F K0) -> ((euclidean__axioms.Cong F K0 G H) -> ((euclidean__defs.TG A B C D E K0) -> ((euclidean__defs.Lt E K0 A J) -> ((K0 = K0) -> ((euclidean__axioms.neq F K0) -> ((euclidean__defs.Out F K0 M) -> ((euclidean__defs.Out F K0 K0) -> ((euclidean__axioms.Cong F K0 F M) -> (euclidean__defs.Lt P L E K0))))))))))) with (x := K).
--------------------------intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
intro H42.
exact H25.

-------------------------- exact H33.
-------------------------- exact H4.
-------------------------- exact H6.
-------------------------- exact H7.
-------------------------- exact H13.
-------------------------- exact H26.
-------------------------- exact H27.
-------------------------- exact H29.
-------------------------- exact H30.
-------------------------- exact H32.
------------------------- assert (* Cut *) (euclidean__defs.Lt P L A J) as H35.
-------------------------- apply (@lemma__lessthantransitive.lemma__lessthantransitive (P) (L) (E) (K) (A) (J) (H34) H13).
-------------------------- assert (* Cut *) (euclidean__defs.TG A B C D P L) as H36.
--------------------------- exists J.
split.
---------------------------- exact H10.
---------------------------- split.
----------------------------- exact H12.
----------------------------- exact H35.
--------------------------- assert (* Cut *) (euclidean__defs.TT A B C D P Q R S) as H37.
---------------------------- exists L.
split.
----------------------------- exact H16.
----------------------------- split.
------------------------------ exact H18.
------------------------------ exact H36.
---------------------------- exact H37.
Qed.
