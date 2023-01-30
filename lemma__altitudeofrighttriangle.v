Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__7.
Require Export lemma__NCdistinct.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__inequalitysymmetric.
Require Export lemma__legsmallerhypotenuse.
Require Export lemma__lessthancongruence2.
Require Export lemma__lessthantransitive.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rightangleNC.
Require Export lemma__trichotomy2.
Require Export lemma__tworays.
Require Export logic.
Definition lemma__altitudeofrighttriangle : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (M: euclidean__axioms.Point) (p: euclidean__axioms.Point), (euclidean__defs.Per B A C) -> ((euclidean__defs.Per A M p) -> ((euclidean__axioms.Col B C p) -> ((euclidean__axioms.Col B C M) -> (euclidean__axioms.BetS B M C)))).
Proof.
intro A.
intro B.
intro C.
intro M.
intro p.
intro H.
intro H0.
intro H1.
intro H2.
assert (* Cut *) (euclidean__axioms.nCol B A C) as H3.
- apply (@lemma__rightangleNC.lemma__rightangleNC (B) (A) (C) H).
- assert (* Cut *) (euclidean__axioms.neq C B) as H4.
-- assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H4.
--- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (A) (C) H3).
--- assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H5.
---- exact H4.
---- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B))))) as H7.
----- exact H6.
----- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))) as H9.
------ exact H8.
------ destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B))) as H11.
------- exact H10.
------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)) as H13.
-------- exact H12.
-------- destruct H13 as [H13 H14].
exact H14.
-- assert (* Cut *) (~(B = M)) as H5.
--- intro H5.
assert (* Cut *) (euclidean__defs.Per A B p) as H6.
---- apply (@eq__ind__r euclidean__axioms.Point M (fun B0: euclidean__axioms.Point => (euclidean__defs.Per B0 A C) -> ((euclidean__axioms.Col B0 C p) -> ((euclidean__axioms.Col B0 C M) -> ((euclidean__axioms.nCol B0 A C) -> ((euclidean__axioms.neq C B0) -> (euclidean__defs.Per A B0 p))))))) with (x := B).
-----intro H6.
intro H7.
intro H8.
intro H9.
intro H10.
exact H0.

----- exact H5.
----- exact H.
----- exact H1.
----- exact H2.
----- exact H3.
----- exact H4.
---- assert (* Cut *) (euclidean__axioms.Col p B C) as H7.
----- assert (* Cut *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H7.
------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (p) H1).
------ assert (* AndElim *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
exact H12.
----- assert (* Cut *) (euclidean__defs.Per p B A) as H8.
------ apply (@lemma__8__2.lemma__8__2 (A) (B) (p) H6).
------ assert (* Cut *) (euclidean__defs.Per C B A) as H9.
------- apply (@lemma__collinearright.lemma__collinearright (p) (B) (C) (A) (H8) (H7) H4).
------- assert (* Cut *) (~(euclidean__defs.Per C B A)) as H10.
-------- apply (@lemma__8__7.lemma__8__7 (C) (A) (B) H).
-------- apply (@H10 H9).
--- assert (* Cut *) (euclidean__defs.Per p M A) as H6.
---- apply (@lemma__8__2.lemma__8__2 (A) (M) (p) H0).
---- assert (* Cut *) (euclidean__axioms.Col C B p) as H7.
----- assert (* Cut *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H7.
------ apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (p) H1).
------ assert (* AndElim *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)))) as H10.
-------- exact H9.
-------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))) as H12.
--------- exact H11.
--------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)) as H14.
---------- exact H13.
---------- destruct H14 as [H14 H15].
exact H8.
----- assert (* Cut *) (euclidean__axioms.Col C B M) as H8.
------ assert (* Cut *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H8.
------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (M) H2).
------- assert (* AndElim *) ((euclidean__axioms.Col C B M) /\ ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))))) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
assert (* AndElim *) ((euclidean__axioms.Col C M B) /\ ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B)))) as H11.
--------- exact H10.
--------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.Col M B C) /\ ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B))) as H13.
---------- exact H12.
---------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col B M C) /\ (euclidean__axioms.Col M C B)) as H15.
----------- exact H14.
----------- destruct H15 as [H15 H16].
exact H9.
------ assert (* Cut *) (euclidean__axioms.nCol B A C) as H9.
------- exact H3.
------- assert (* Cut *) (euclidean__axioms.neq C B) as H10.
-------- assert (* Cut *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H10.
--------- apply (@lemma__NCdistinct.lemma__NCdistinct (B) (A) (C) H9).
--------- assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))))) as H11.
---------- exact H10.
---------- destruct H11 as [H11 H12].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B))))) as H13.
----------- exact H12.
----------- destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)))) as H15.
------------ exact H14.
------------ destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B))) as H17.
------------- exact H16.
------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ (euclidean__axioms.neq C B)) as H19.
-------------- exact H18.
-------------- destruct H19 as [H19 H20].
exact H20.
-------- assert (* Cut *) (euclidean__axioms.Col B p M) as H11.
--------- apply (@euclidean__tactics.not__nCol__Col (B) (p) (M)).
----------intro H11.
apply (@euclidean__tactics.Col__nCol__False (B) (p) (M) (H11)).
-----------apply (@lemma__collinear4.lemma__collinear4 (C) (B) (p) (M) (H7) (H8) H10).


--------- assert (* Cut *) (euclidean__axioms.Col p M B) as H12.
---------- assert (* Cut *) ((euclidean__axioms.Col p B M) /\ ((euclidean__axioms.Col p M B) /\ ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B M p) /\ (euclidean__axioms.Col M p B))))) as H12.
----------- apply (@lemma__collinearorder.lemma__collinearorder (B) (p) (M) H11).
----------- assert (* AndElim *) ((euclidean__axioms.Col p B M) /\ ((euclidean__axioms.Col p M B) /\ ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B M p) /\ (euclidean__axioms.Col M p B))))) as H13.
------------ exact H12.
------------ destruct H13 as [H13 H14].
assert (* AndElim *) ((euclidean__axioms.Col p M B) /\ ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B M p) /\ (euclidean__axioms.Col M p B)))) as H15.
------------- exact H14.
------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B M p) /\ (euclidean__axioms.Col M p B))) as H17.
-------------- exact H16.
-------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col B M p) /\ (euclidean__axioms.Col M p B)) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
exact H15.
---------- assert (* Cut *) (euclidean__defs.Per B M A) as H13.
----------- apply (@lemma__collinearright.lemma__collinearright (p) (M) (B) (A) (H6) (H12) H5).
----------- assert (* Cut *) (euclidean__axioms.Col B C p) as H14.
------------ assert (* Cut *) ((euclidean__axioms.Col M p B) /\ ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B p M) /\ ((euclidean__axioms.Col p B M) /\ (euclidean__axioms.Col B M p))))) as H14.
------------- apply (@lemma__collinearorder.lemma__collinearorder (p) (M) (B) H12).
------------- assert (* AndElim *) ((euclidean__axioms.Col M p B) /\ ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B p M) /\ ((euclidean__axioms.Col p B M) /\ (euclidean__axioms.Col B M p))))) as H15.
-------------- exact H14.
-------------- destruct H15 as [H15 H16].
assert (* AndElim *) ((euclidean__axioms.Col M B p) /\ ((euclidean__axioms.Col B p M) /\ ((euclidean__axioms.Col p B M) /\ (euclidean__axioms.Col B M p)))) as H17.
--------------- exact H16.
--------------- destruct H17 as [H17 H18].
assert (* AndElim *) ((euclidean__axioms.Col B p M) /\ ((euclidean__axioms.Col p B M) /\ (euclidean__axioms.Col B M p))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col p B M) /\ (euclidean__axioms.Col B M p)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
exact H1.
------------ assert (* Cut *) (euclidean__axioms.Col B C M) as H15.
------------- assert (* Cut *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H15.
-------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (p) H14).
-------------- assert (* AndElim *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H16.
--------------- exact H15.
--------------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)))) as H18.
---------------- exact H17.
---------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
exact H2.
------------- assert (* Cut *) (euclidean__axioms.neq B C) as H16.
-------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (C) (B) H10).
-------------- assert (* Cut *) (euclidean__axioms.Col C p M) as H17.
--------------- apply (@euclidean__tactics.not__nCol__Col (C) (p) (M)).
----------------intro H17.
apply (@euclidean__tactics.Col__nCol__False (C) (p) (M) (H17)).
-----------------apply (@lemma__collinear4.lemma__collinear4 (B) (C) (p) (M) (H14) (H15) H16).


--------------- assert (* Cut *) (euclidean__axioms.Col p M C) as H18.
---------------- assert (* Cut *) ((euclidean__axioms.Col p C M) /\ ((euclidean__axioms.Col p M C) /\ ((euclidean__axioms.Col M C p) /\ ((euclidean__axioms.Col C M p) /\ (euclidean__axioms.Col M p C))))) as H18.
----------------- apply (@lemma__collinearorder.lemma__collinearorder (C) (p) (M) H17).
----------------- assert (* AndElim *) ((euclidean__axioms.Col p C M) /\ ((euclidean__axioms.Col p M C) /\ ((euclidean__axioms.Col M C p) /\ ((euclidean__axioms.Col C M p) /\ (euclidean__axioms.Col M p C))))) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.Col p M C) /\ ((euclidean__axioms.Col M C p) /\ ((euclidean__axioms.Col C M p) /\ (euclidean__axioms.Col M p C)))) as H21.
------------------- exact H20.
------------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col M C p) /\ ((euclidean__axioms.Col C M p) /\ (euclidean__axioms.Col M p C))) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col C M p) /\ (euclidean__axioms.Col M p C)) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
exact H21.
---------------- assert (* Cut *) (euclidean__defs.Per C A B) as H19.
----------------- apply (@lemma__8__2.lemma__8__2 (B) (A) (C) H).
----------------- assert (* Cut *) (~(C = M)) as H20.
------------------ intro H20.
assert (* Cut *) (euclidean__defs.Per A C p) as H21.
------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun C0: euclidean__axioms.Point => (euclidean__defs.Per B A C0) -> ((euclidean__axioms.Col B C0 p) -> ((euclidean__axioms.Col B C0 M) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Col C0 B p) -> ((euclidean__axioms.Col C0 B M) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Col B C0 p) -> ((euclidean__axioms.Col B C0 M) -> ((euclidean__axioms.neq B C0) -> ((euclidean__axioms.Col C0 p M) -> ((euclidean__axioms.Col p M C0) -> ((euclidean__defs.Per C0 A B) -> (euclidean__defs.Per A C0 p))))))))))))))))) with (x := C).
--------------------intro H21.
intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
exact H0.

-------------------- exact H20.
-------------------- exact H.
-------------------- exact H1.
-------------------- exact H2.
-------------------- exact H3.
-------------------- exact H4.
-------------------- exact H7.
-------------------- exact H8.
-------------------- exact H9.
-------------------- exact H10.
-------------------- exact H14.
-------------------- exact H15.
-------------------- exact H16.
-------------------- exact H17.
-------------------- exact H18.
-------------------- exact H19.
------------------- assert (* Cut *) (euclidean__axioms.Col p C B) as H22.
-------------------- assert (* Cut *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H22.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (p) H14).
--------------------- assert (* AndElim *) ((euclidean__axioms.Col C B p) /\ ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))))) as H23.
---------------------- exact H22.
---------------------- destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.Col C p B) /\ ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)))) as H25.
----------------------- exact H24.
----------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col p B C) /\ ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B))) as H27.
------------------------ exact H26.
------------------------ destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col B p C) /\ (euclidean__axioms.Col p C B)) as H29.
------------------------- exact H28.
------------------------- destruct H29 as [H29 H30].
exact H30.
-------------------- assert (* Cut *) (euclidean__defs.Per p C A) as H23.
--------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun C0: euclidean__axioms.Point => (euclidean__defs.Per B A C0) -> ((euclidean__axioms.Col B C0 p) -> ((euclidean__axioms.Col B C0 M) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Col C0 B p) -> ((euclidean__axioms.Col C0 B M) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Col B C0 p) -> ((euclidean__axioms.Col B C0 M) -> ((euclidean__axioms.neq B C0) -> ((euclidean__axioms.Col C0 p M) -> ((euclidean__axioms.Col p M C0) -> ((euclidean__defs.Per C0 A B) -> ((euclidean__defs.Per A C0 p) -> ((euclidean__axioms.Col p C0 B) -> (euclidean__defs.Per p C0 A))))))))))))))))))) with (x := C).
----------------------intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
exact H6.

---------------------- exact H20.
---------------------- exact H.
---------------------- exact H1.
---------------------- exact H2.
---------------------- exact H3.
---------------------- exact H4.
---------------------- exact H7.
---------------------- exact H8.
---------------------- exact H9.
---------------------- exact H10.
---------------------- exact H14.
---------------------- exact H15.
---------------------- exact H16.
---------------------- exact H17.
---------------------- exact H18.
---------------------- exact H19.
---------------------- exact H21.
---------------------- exact H22.
--------------------- assert (* Cut *) (euclidean__defs.Per B C A) as H24.
---------------------- apply (@eq__ind__r euclidean__axioms.Point M (fun C0: euclidean__axioms.Point => (euclidean__defs.Per B A C0) -> ((euclidean__axioms.Col B C0 p) -> ((euclidean__axioms.Col B C0 M) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Col C0 B p) -> ((euclidean__axioms.Col C0 B M) -> ((euclidean__axioms.nCol B A C0) -> ((euclidean__axioms.neq C0 B) -> ((euclidean__axioms.Col B C0 p) -> ((euclidean__axioms.Col B C0 M) -> ((euclidean__axioms.neq B C0) -> ((euclidean__axioms.Col C0 p M) -> ((euclidean__axioms.Col p M C0) -> ((euclidean__defs.Per C0 A B) -> ((euclidean__defs.Per A C0 p) -> ((euclidean__axioms.Col p C0 B) -> ((euclidean__defs.Per p C0 A) -> (euclidean__defs.Per B C0 A)))))))))))))))))))) with (x := C).
-----------------------intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
intro H29.
intro H30.
intro H31.
intro H32.
intro H33.
intro H34.
intro H35.
intro H36.
intro H37.
intro H38.
intro H39.
intro H40.
intro H41.
exact H13.

----------------------- exact H20.
----------------------- exact H.
----------------------- exact H1.
----------------------- exact H2.
----------------------- exact H3.
----------------------- exact H4.
----------------------- exact H7.
----------------------- exact H8.
----------------------- exact H9.
----------------------- exact H10.
----------------------- exact H14.
----------------------- exact H15.
----------------------- exact H16.
----------------------- exact H17.
----------------------- exact H18.
----------------------- exact H19.
----------------------- exact H21.
----------------------- exact H22.
----------------------- exact H23.
---------------------- assert (* Cut *) (~(euclidean__defs.Per B C A)) as H25.
----------------------- apply (@lemma__8__7.lemma__8__7 (B) (A) (C) H19).
----------------------- apply (@H25 H24).
------------------ assert (* Cut *) (euclidean__defs.Per C M A) as H21.
------------------- apply (@lemma__collinearright.lemma__collinearright (p) (M) (C) (A) (H6) (H18) H20).
------------------- assert (* Cut *) (euclidean__defs.Per A M B) as H22.
-------------------- apply (@lemma__8__2.lemma__8__2 (B) (M) (A) H13).
-------------------- assert (* Cut *) (euclidean__defs.Per A M C) as H23.
--------------------- apply (@lemma__8__2.lemma__8__2 (C) (M) (A) H21).
--------------------- assert (* Cut *) (euclidean__defs.Lt M B A B) as H24.
---------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point), (euclidean__defs.Per A0 B0 C0) -> (euclidean__defs.Lt B0 C0 A0 C0)) as H24.
----------------------- intro A0.
intro B0.
intro C0.
intro __.
assert (* AndElim *) ((euclidean__defs.Lt A0 B0 A0 C0) /\ (euclidean__defs.Lt B0 C0 A0 C0)) as __0.
------------------------ apply (@lemma__legsmallerhypotenuse.lemma__legsmallerhypotenuse (A0) (B0) (C0) __).
------------------------ destruct __0 as [__0 __1].
exact __1.
----------------------- apply (@H24 (A) (M) (B) H22).
---------------------- assert (* Cut *) (euclidean__defs.Lt B A B C) as H25.
----------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point), (euclidean__defs.Per A0 B0 C0) -> (euclidean__defs.Lt A0 B0 A0 C0)) as H25.
------------------------ intro A0.
intro B0.
intro C0.
intro __.
assert (* AndElim *) ((euclidean__defs.Lt A0 B0 A0 C0) /\ (euclidean__defs.Lt B0 C0 A0 C0)) as __0.
------------------------- apply (@lemma__legsmallerhypotenuse.lemma__legsmallerhypotenuse (A0) (B0) (C0) __).
------------------------- destruct __0 as [__0 __1].
exact __0.
------------------------ apply (@H25 (B) (A) (C) H).
----------------------- assert (* Cut *) (euclidean__axioms.Cong B A A B) as H26.
------------------------ apply (@euclidean__axioms.cn__equalityreverse (B) A).
------------------------ assert (* Cut *) (euclidean__defs.Lt A B B C) as H27.
------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (B) (A) (B) (C) (A) (B) (H25) H26).
------------------------- assert (* Cut *) (euclidean__defs.Lt M B B C) as H28.
-------------------------- apply (@lemma__lessthantransitive.lemma__lessthantransitive (M) (B) (A) (B) (B) (C) (H24) H27).
-------------------------- assert (* Cut *) (euclidean__axioms.Cong M B B M) as H29.
--------------------------- apply (@euclidean__axioms.cn__equalityreverse (M) B).
--------------------------- assert (* Cut *) (euclidean__defs.Lt B M B C) as H30.
---------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (M) (B) (B) (C) (B) (M) (H28) H29).
---------------------------- assert (* Cut *) (euclidean__defs.Lt M C A C) as H31.
----------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point), (euclidean__defs.Per A0 B0 C0) -> (euclidean__defs.Lt B0 C0 A0 C0)) as H31.
------------------------------ intro A0.
intro B0.
intro C0.
intro __.
assert (* AndElim *) ((euclidean__defs.Lt A0 B0 A0 C0) /\ (euclidean__defs.Lt B0 C0 A0 C0)) as __0.
------------------------------- apply (@lemma__legsmallerhypotenuse.lemma__legsmallerhypotenuse (A0) (B0) (C0) __).
------------------------------- destruct __0 as [__0 __1].
exact __1.
------------------------------ apply (@H31 (A) (M) (C) H23).
----------------------------- assert (* Cut *) (euclidean__axioms.Cong M C C M) as H32.
------------------------------ apply (@euclidean__axioms.cn__equalityreverse (M) C).
------------------------------ assert (* Cut *) (euclidean__defs.Lt C M A C) as H33.
------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (M) (C) (A) (C) (C) (M) (H31) H32).
------------------------------- assert (* Cut *) (euclidean__defs.Lt A C B C) as H34.
-------------------------------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point), (euclidean__defs.Per A0 B0 C0) -> (euclidean__defs.Lt B0 C0 A0 C0)) as H34.
--------------------------------- intro A0.
intro B0.
intro C0.
intro __.
assert (* AndElim *) ((euclidean__defs.Lt A0 B0 A0 C0) /\ (euclidean__defs.Lt B0 C0 A0 C0)) as __0.
---------------------------------- apply (@lemma__legsmallerhypotenuse.lemma__legsmallerhypotenuse (A0) (B0) (C0) __).
---------------------------------- destruct __0 as [__0 __1].
exact __1.
--------------------------------- apply (@H34 (B) (A) (C) H).
-------------------------------- assert (* Cut *) (euclidean__defs.Lt C M B C) as H35.
--------------------------------- apply (@lemma__lessthantransitive.lemma__lessthantransitive (C) (M) (A) (C) (B) (C) (H33) H34).
--------------------------------- assert (* Cut *) (~(euclidean__axioms.BetS M B C)) as H36.
---------------------------------- intro H36.
assert (* Cut *) (euclidean__axioms.BetS C B M) as H37.
----------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (M) (B) (C) H36).
----------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B C B) as H38.
------------------------------------ apply (@euclidean__axioms.cn__congruencereflexive (C) B).
------------------------------------ assert (* Cut *) (euclidean__defs.Lt C B C M) as H39.
------------------------------------- exists B.
split.
-------------------------------------- exact H37.
-------------------------------------- exact H38.
------------------------------------- assert (* Cut *) (euclidean__axioms.Cong C B B C) as H40.
-------------------------------------- apply (@euclidean__axioms.cn__equalityreverse (C) B).
-------------------------------------- assert (* Cut *) (euclidean__defs.Lt B C C M) as H41.
--------------------------------------- apply (@lemma__lessthancongruence2.lemma__lessthancongruence2 (C) (B) (C) (M) (B) (C) (H39) H40).
--------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt C M B C)) as H42.
---------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 (B) (C) (C) (M) H41).
---------------------------------------- apply (@H42 H35).
---------------------------------- assert (* Cut *) ((B = C) \/ ((B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))))) as H37.
----------------------------------- exact H15.
----------------------------------- assert (* Cut *) (euclidean__defs.Out B C M) as H38.
------------------------------------ assert (* Cut *) ((B = C) \/ ((B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))))) as H38.
------------------------------------- exact H37.
------------------------------------- assert (* Cut *) ((B = C) \/ ((B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))))) as __TmpHyp.
-------------------------------------- exact H38.
-------------------------------------- assert (B = C \/ (B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C))))) as H39.
--------------------------------------- exact __TmpHyp.
--------------------------------------- destruct H39 as [H39|H39].
---------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C M))) as H40.
----------------------------------------- intro H40.
apply (@H16 H39).
----------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C M)).
------------------------------------------intro H41.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H42.
------------------------------------------- exact H3.
------------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H44.
-------------------------------------------- exact H9.
-------------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H46.
--------------------------------------------- exact H43.
--------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H48.
---------------------------------------------- exact H45.
---------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H50.
----------------------------------------------- exact H47.
----------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H52.
------------------------------------------------ exact H49.
------------------------------------------------ destruct H52 as [H52 H53].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H54.
------------------------------------------------- exact H51.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H56.
-------------------------------------------------- exact H53.
-------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H58.
--------------------------------------------------- exact H55.
--------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H60.
---------------------------------------------------- exact H57.
---------------------------------------------------- destruct H60 as [H60 H61].
assert (* Cut *) (False) as H62.
----------------------------------------------------- apply (@H16 H39).
----------------------------------------------------- assert (* Cut *) (False) as H63.
------------------------------------------------------ apply (@H40 H41).
------------------------------------------------------ assert False.
-------------------------------------------------------exact H63.
------------------------------------------------------- contradiction.

---------------------------------------- assert (B = M \/ (C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))) as H40.
----------------------------------------- exact H39.
----------------------------------------- destruct H40 as [H40|H40].
------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.Out B C M))) as H41.
------------------------------------------- intro H41.
apply (@H5 H40).
------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C M)).
--------------------------------------------intro H42.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H43.
--------------------------------------------- exact H3.
--------------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H45.
---------------------------------------------- exact H9.
---------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H47.
----------------------------------------------- exact H44.
----------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H49.
------------------------------------------------ exact H46.
------------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H51.
------------------------------------------------- exact H48.
------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H53.
-------------------------------------------------- exact H50.
-------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H55.
--------------------------------------------------- exact H52.
--------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H57.
---------------------------------------------------- exact H54.
---------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H59.
----------------------------------------------------- exact H56.
----------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H61.
------------------------------------------------------ exact H58.
------------------------------------------------------ destruct H61 as [H61 H62].
assert (* Cut *) (False) as H63.
------------------------------------------------------- apply (@H5 H40).
------------------------------------------------------- assert (* Cut *) (False) as H64.
-------------------------------------------------------- apply (@H41 H42).
-------------------------------------------------------- assert False.
---------------------------------------------------------exact H64.
--------------------------------------------------------- contradiction.

------------------------------------------ assert (C = M \/ (euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C))) as H41.
------------------------------------------- exact H40.
------------------------------------------- destruct H41 as [H41|H41].
-------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C M))) as H42.
--------------------------------------------- intro H42.
apply (@H20 H41).
--------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C M)).
----------------------------------------------intro H43.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H44.
----------------------------------------------- exact H3.
----------------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H46.
------------------------------------------------ exact H9.
------------------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H48.
------------------------------------------------- exact H45.
------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H50.
-------------------------------------------------- exact H47.
-------------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H52.
--------------------------------------------------- exact H49.
--------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H54.
---------------------------------------------------- exact H51.
---------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H56.
----------------------------------------------------- exact H53.
----------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H58.
------------------------------------------------------ exact H55.
------------------------------------------------------ destruct H58 as [H58 H59].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H60.
------------------------------------------------------- exact H57.
------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H62.
-------------------------------------------------------- exact H59.
-------------------------------------------------------- destruct H62 as [H62 H63].
assert (* Cut *) (False) as H64.
--------------------------------------------------------- apply (@H20 H41).
--------------------------------------------------------- assert (* Cut *) (False) as H65.
---------------------------------------------------------- apply (@H42 H43).
---------------------------------------------------------- assert False.
-----------------------------------------------------------exact H65.
----------------------------------------------------------- contradiction.

-------------------------------------------- assert (euclidean__axioms.BetS C B M \/ (euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)) as H42.
--------------------------------------------- exact H41.
--------------------------------------------- destruct H42 as [H42|H42].
---------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out B C M))) as H43.
----------------------------------------------- intro H43.
assert (* Cut *) (euclidean__axioms.BetS M B C) as H44.
------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (C) (B) (M) H42).
------------------------------------------------ apply (@H36 H44).
----------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out B C M)).
------------------------------------------------intro H44.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H45.
------------------------------------------------- exact H3.
------------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H47.
-------------------------------------------------- exact H9.
-------------------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H49.
--------------------------------------------------- exact H46.
--------------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H51.
---------------------------------------------------- exact H48.
---------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H53.
----------------------------------------------------- exact H50.
----------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H55.
------------------------------------------------------ exact H52.
------------------------------------------------------ destruct H55 as [H55 H56].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H57.
------------------------------------------------------- exact H54.
------------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H59.
-------------------------------------------------------- exact H56.
-------------------------------------------------------- destruct H59 as [H59 H60].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H61.
--------------------------------------------------------- exact H58.
--------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H63.
---------------------------------------------------------- exact H60.
---------------------------------------------------------- destruct H63 as [H63 H64].
assert (* Cut *) (False) as H65.
----------------------------------------------------------- apply (@H43 H44).
----------------------------------------------------------- assert False.
------------------------------------------------------------exact H65.
------------------------------------------------------------ contradiction.

---------------------------------------------- assert (euclidean__axioms.BetS B C M \/ euclidean__axioms.BetS B M C) as H43.
----------------------------------------------- exact H42.
----------------------------------------------- destruct H43 as [H43|H43].
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B C M) as H44.
------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (C) (M)).
--------------------------------------------------right.
right.
exact H43.

-------------------------------------------------- exact H16.
------------------------------------------------- exact H44.
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out B M C) as H44.
------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (M) (C)).
--------------------------------------------------right.
right.
exact H43.

-------------------------------------------------- exact H5.
------------------------------------------------- assert (* Cut *) (euclidean__defs.Out B C M) as H45.
-------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (M) (C) H44).
-------------------------------------------------- exact H45.
------------------------------------ assert (* Cut *) (~(euclidean__axioms.BetS B C M)) as H39.
------------------------------------- intro H39.
assert (* Cut *) (euclidean__axioms.Cong B C B C) as H40.
-------------------------------------- apply (@euclidean__axioms.cn__congruencereflexive (B) C).
-------------------------------------- assert (* Cut *) (euclidean__defs.Lt B C B M) as H41.
--------------------------------------- exists C.
split.
---------------------------------------- exact H39.
---------------------------------------- exact H40.
--------------------------------------- assert (* Cut *) (~(euclidean__defs.Lt B M B C)) as H42.
---------------------------------------- apply (@lemma__trichotomy2.lemma__trichotomy2 (B) (C) (B) (M) H41).
---------------------------------------- apply (@H42 H30).
------------------------------------- assert (* Cut *) (euclidean__defs.Out C B M) as H40.
-------------------------------------- assert (* Cut *) ((B = C) \/ ((B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))))) as H40.
--------------------------------------- exact H37.
--------------------------------------- assert (* Cut *) ((B = C) \/ ((B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))))) as __TmpHyp.
---------------------------------------- exact H40.
---------------------------------------- assert (B = C \/ (B = M) \/ ((C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C))))) as H41.
----------------------------------------- exact __TmpHyp.
----------------------------------------- destruct H41 as [H41|H41].
------------------------------------------ assert (* Cut *) (~(~(euclidean__defs.Out C B M))) as H42.
------------------------------------------- intro H42.
apply (@H16 H41).
------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out C B M)).
--------------------------------------------intro H43.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H44.
--------------------------------------------- exact H3.
--------------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H46.
---------------------------------------------- exact H9.
---------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H48.
----------------------------------------------- exact H45.
----------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H50.
------------------------------------------------ exact H47.
------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H52.
------------------------------------------------- exact H49.
------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H54.
-------------------------------------------------- exact H51.
-------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H56.
--------------------------------------------------- exact H53.
--------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H58.
---------------------------------------------------- exact H55.
---------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H60.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H62.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H62 as [H62 H63].
assert (* Cut *) (False) as H64.
------------------------------------------------------- apply (@H16 H41).
------------------------------------------------------- assert (* Cut *) (False) as H65.
-------------------------------------------------------- apply (@H42 H43).
-------------------------------------------------------- assert False.
---------------------------------------------------------exact H65.
--------------------------------------------------------- contradiction.

------------------------------------------ assert (B = M \/ (C = M) \/ ((euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)))) as H42.
------------------------------------------- exact H41.
------------------------------------------- destruct H42 as [H42|H42].
-------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out C B M))) as H43.
--------------------------------------------- intro H43.
apply (@H5 H42).
--------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out C B M)).
----------------------------------------------intro H44.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H45.
----------------------------------------------- exact H3.
----------------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H47.
------------------------------------------------ exact H9.
------------------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H49.
------------------------------------------------- exact H46.
------------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H51.
-------------------------------------------------- exact H48.
-------------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H53.
--------------------------------------------------- exact H50.
--------------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H55.
---------------------------------------------------- exact H52.
---------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H57.
----------------------------------------------------- exact H54.
----------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H59.
------------------------------------------------------ exact H56.
------------------------------------------------------ destruct H59 as [H59 H60].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H61.
------------------------------------------------------- exact H58.
------------------------------------------------------- destruct H61 as [H61 H62].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H63.
-------------------------------------------------------- exact H60.
-------------------------------------------------------- destruct H63 as [H63 H64].
assert (* Cut *) (False) as H65.
--------------------------------------------------------- apply (@H5 H42).
--------------------------------------------------------- assert (* Cut *) (False) as H66.
---------------------------------------------------------- apply (@H43 H44).
---------------------------------------------------------- assert False.
-----------------------------------------------------------exact H66.
----------------------------------------------------------- contradiction.

-------------------------------------------- assert (C = M \/ (euclidean__axioms.BetS C B M) \/ ((euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C))) as H43.
--------------------------------------------- exact H42.
--------------------------------------------- destruct H43 as [H43|H43].
---------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out C B M))) as H44.
----------------------------------------------- intro H44.
apply (@H20 H43).
----------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out C B M)).
------------------------------------------------intro H45.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H46.
------------------------------------------------- exact H3.
------------------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H48.
-------------------------------------------------- exact H9.
-------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H50.
--------------------------------------------------- exact H47.
--------------------------------------------------- destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H52.
---------------------------------------------------- exact H49.
---------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H54.
----------------------------------------------------- exact H51.
----------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H56.
------------------------------------------------------ exact H53.
------------------------------------------------------ destruct H56 as [H56 H57].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H58.
------------------------------------------------------- exact H55.
------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H60.
-------------------------------------------------------- exact H57.
-------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H62.
--------------------------------------------------------- exact H59.
--------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H64.
---------------------------------------------------------- exact H61.
---------------------------------------------------------- destruct H64 as [H64 H65].
assert (* Cut *) (False) as H66.
----------------------------------------------------------- apply (@H20 H43).
----------------------------------------------------------- assert (* Cut *) (False) as H67.
------------------------------------------------------------ apply (@H44 H45).
------------------------------------------------------------ assert False.
-------------------------------------------------------------exact H67.
------------------------------------------------------------- contradiction.

---------------------------------------------- assert (euclidean__axioms.BetS C B M \/ (euclidean__axioms.BetS B C M) \/ (euclidean__axioms.BetS B M C)) as H44.
----------------------------------------------- exact H43.
----------------------------------------------- destruct H44 as [H44|H44].
------------------------------------------------ assert (* Cut *) (euclidean__defs.Out C B M) as H45.
------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (B) (M)).
--------------------------------------------------right.
right.
exact H44.

-------------------------------------------------- exact H10.
------------------------------------------------- exact H45.
------------------------------------------------ assert (euclidean__axioms.BetS B C M \/ euclidean__axioms.BetS B M C) as H45.
------------------------------------------------- exact H44.
------------------------------------------------- destruct H45 as [H45|H45].
-------------------------------------------------- assert (* Cut *) (~(~(euclidean__defs.Out C B M))) as H46.
--------------------------------------------------- intro H46.
apply (@H39 H45).
--------------------------------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.Out C B M)).
----------------------------------------------------intro H47.
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H48.
----------------------------------------------------- exact H3.
----------------------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))))) as H50.
------------------------------------------------------ exact H9.
------------------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H52.
------------------------------------------------------- exact H49.
------------------------------------------------------- destruct H52 as [H52 H53].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))))) as H54.
-------------------------------------------------------- exact H51.
-------------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H56.
--------------------------------------------------------- exact H53.
--------------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))))) as H58.
---------------------------------------------------------- exact H55.
---------------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H60.
----------------------------------------------------------- exact H57.
----------------------------------------------------------- destruct H60 as [H60 H61].
assert (* AndElim *) ((~(euclidean__axioms.BetS B A C)) /\ ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C)))) as H62.
------------------------------------------------------------ exact H59.
------------------------------------------------------------ destruct H62 as [H62 H63].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H64.
------------------------------------------------------------- exact H61.
------------------------------------------------------------- destruct H64 as [H64 H65].
assert (* AndElim *) ((~(euclidean__axioms.BetS B C A)) /\ (~(euclidean__axioms.BetS A B C))) as H66.
-------------------------------------------------------------- exact H63.
-------------------------------------------------------------- destruct H66 as [H66 H67].
assert (* Cut *) (False) as H68.
--------------------------------------------------------------- apply (@H39 H45).
--------------------------------------------------------------- assert (* Cut *) (False) as H69.
---------------------------------------------------------------- apply (@H46 H47).
---------------------------------------------------------------- assert False.
-----------------------------------------------------------------exact H69.
----------------------------------------------------------------- contradiction.

-------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS C M B) as H46.
--------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (C) H45).
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C M B) as H47.
---------------------------------------------------- apply (@lemma__ray4.lemma__ray4 (C) (M) (B)).
-----------------------------------------------------right.
right.
exact H46.

----------------------------------------------------- exact H20.
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Out C B M) as H48.
----------------------------------------------------- apply (@lemma__ray5.lemma__ray5 (C) (M) (B) H47).
----------------------------------------------------- exact H48.
-------------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M C) as H41.
--------------------------------------- apply (@lemma__tworays.lemma__tworays (B) (C) (M) (H38) H40).
--------------------------------------- exact H41.
Qed.
