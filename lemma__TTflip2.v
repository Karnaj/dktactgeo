Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__betweennotequal.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__lessthancongruence2.
Require Export logic.
Definition lemma__TTflip2 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point), (euclidean__defs.TT A B C D E F G H) -> (euclidean__defs.TT A B C D H G F E).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro H0.
assert (* Cut *) (exists (J: euclidean__axioms.Point), (euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J))) as H1.
- exact H0.
- assert (exists J: euclidean__axioms.Point, ((euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J)))) as H2.
-- exact H1.
-- destruct H2 as [J H2].
assert (* AndElim *) ((euclidean__axioms.BetS E F J) /\ ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J))) as H3.
--- exact H2.
--- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__axioms.Cong F J G H) /\ (euclidean__defs.TG A B C D E J)) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* Cut *) (exists (K: euclidean__axioms.Point), (euclidean__axioms.BetS A B K) /\ ((euclidean__axioms.Cong B K C D) /\ (euclidean__defs.Lt E J A K))) as H7.
----- exact H6.
----- assert (exists K: euclidean__axioms.Point, ((euclidean__axioms.BetS A B K) /\ ((euclidean__axioms.Cong B K C D) /\ (euclidean__defs.Lt E J A K)))) as H8.
------ exact H7.
------ destruct H8 as [K H8].
assert (* AndElim *) ((euclidean__axioms.BetS A B K) /\ ((euclidean__axioms.Cong B K C D) /\ (euclidean__defs.Lt E J A K))) as H9.
------- exact H8.
------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Cong B K C D) /\ (euclidean__defs.Lt E J A K)) as H11.
-------- exact H10.
-------- destruct H11 as [H11 H12].
assert (* Cut *) (euclidean__axioms.neq F J) as H13.
--------- assert (* Cut *) ((euclidean__axioms.neq F J) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E J))) as H13.
---------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (F) (J) H3).
---------- assert (* AndElim *) ((euclidean__axioms.neq F J) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E J))) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E J)) as H16.
------------ exact H15.
------------ destruct H16 as [H16 H17].
exact H14.
--------- assert (* Cut *) (euclidean__axioms.neq G H) as H14.
---------- apply (@euclidean__axioms.axiom__nocollapse (F) (J) (G) (H) (H13) H5).
---------- assert (* Cut *) (euclidean__axioms.neq H G) as H15.
----------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (G) (H) H14).
----------- assert (* Cut *) (euclidean__axioms.neq E F) as H16.
------------ assert (* Cut *) ((euclidean__axioms.neq F J) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E J))) as H16.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal (E) (F) (J) H3).
------------- assert (* AndElim *) ((euclidean__axioms.neq F J) /\ ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E J))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq E F) /\ (euclidean__axioms.neq E J)) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
exact H19.
------------ assert (* Cut *) (euclidean__axioms.neq F E) as H17.
------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (E) (F) H16).
------------- assert (* Cut *) (exists (L: euclidean__axioms.Point), (euclidean__axioms.BetS H G L) /\ (euclidean__axioms.Cong G L F E)) as H18.
-------------- apply (@lemma__extension.lemma__extension (H) (G) (F) (E) (H15) H17).
-------------- assert (exists L: euclidean__axioms.Point, ((euclidean__axioms.BetS H G L) /\ (euclidean__axioms.Cong G L F E))) as H19.
--------------- exact H18.
--------------- destruct H19 as [L H19].
assert (* AndElim *) ((euclidean__axioms.BetS H G L) /\ (euclidean__axioms.Cong G L F E)) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* Cut *) (euclidean__axioms.Cong L G E F) as H22.
----------------- assert (* Cut *) ((euclidean__axioms.Cong L G E F) /\ ((euclidean__axioms.Cong L G F E) /\ (euclidean__axioms.Cong G L E F))) as H22.
------------------ apply (@lemma__congruenceflip.lemma__congruenceflip (G) (L) (F) (E) H21).
------------------ assert (* AndElim *) ((euclidean__axioms.Cong L G E F) /\ ((euclidean__axioms.Cong L G F E) /\ (euclidean__axioms.Cong G L E F))) as H23.
------------------- exact H22.
------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Cong L G F E) /\ (euclidean__axioms.Cong G L E F)) as H25.
-------------------- exact H24.
-------------------- destruct H25 as [H25 H26].
exact H23.
----------------- assert (* Cut *) (euclidean__axioms.Cong G H F J) as H23.
------------------ apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (G) (F) (J) (H) H5).
------------------ assert (* Cut *) (euclidean__axioms.BetS L G H) as H24.
------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (H) (G) (L) H20).
------------------- assert (* Cut *) (euclidean__axioms.Cong L H E J) as H25.
-------------------- apply (@euclidean__axioms.cn__sumofparts (L) (G) (H) (E) (F) (J) (H22) (H23) (H24) H3).
-------------------- assert (* Cut *) (euclidean__axioms.Cong H L L H) as H26.
--------------------- apply (@euclidean__axioms.cn__equalityreverse (H) L).
--------------------- assert (* Cut *) (euclidean__axioms.Cong H L E J) as H27.
---------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive (H) (L) (L) (H) (E) (J) (H26) H25).
---------------------- assert (* Cut *) (euclidean__axioms.Cong E J H L) as H28.
----------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric (E) (H) (L) (J) H27).
----------------------- assert (* Cut *) (euclidean__defs.Lt H L A K) as H29.
------------------------ apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (E) (J) (A) (K) (H) (L) (H12) H28).
------------------------ assert (* Cut *) (euclidean__defs.TG A B C D H L) as H30.
------------------------- exists K.
split.
-------------------------- exact H9.
-------------------------- split.
--------------------------- exact H11.
--------------------------- exact H29.
------------------------- assert (* Cut *) (euclidean__defs.TT A B C D H G F E) as H31.
-------------------------- exists L.
split.
--------------------------- exact H20.
--------------------------- split.
---------------------------- exact H21.
---------------------------- exact H30.
-------------------------- exact H31.
Qed.
