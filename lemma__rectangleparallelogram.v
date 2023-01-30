Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__8__2.
Require Export lemma__8__7.
Require Export lemma__NCdistinct.
Require Export lemma__collinearorder.
Require Export lemma__collinearright.
Require Export lemma__inequalitysymmetric.
Require Export lemma__rightangleNC.
Require Export logic.
Definition lemma__rectangleparallelogram : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point), (euclidean__defs.RE A B C D) -> (euclidean__defs.PG A B C D).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H0.
- assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H0.
-- exact H.
-- assert (* Cut *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as __TmpHyp.
--- exact H0.
--- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H1.
---- exact __TmpHyp.
---- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H3.
----- exact H2.
----- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
split.
-------- exact H1.
-------- split.
--------- exact H3.
--------- split.
---------- exact H5.
---------- split.
----------- exact H7.
----------- exact H8.
- assert (* Cut *) (euclidean__axioms.nCol D A B) as H1.
-- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H1.
--- exact H0.
--- destruct H1 as [H1 H2].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H3.
---- exact H2.
---- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H5.
----- exact H4.
----- destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H7.
------ exact H6.
------ destruct H7 as [H7 H8].
apply (@lemma__rightangleNC.lemma__rightangleNC (D) (A) (B) H1).
-- assert (* Cut *) (euclidean__axioms.nCol A B C) as H2.
--- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H2.
---- exact H0.
---- destruct H2 as [H2 H3].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H4.
----- exact H3.
----- destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H6.
------ exact H5.
------ destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H8.
------- exact H7.
------- destruct H8 as [H8 H9].
apply (@lemma__rightangleNC.lemma__rightangleNC (A) (B) (C) H4).
--- assert (* Cut *) (euclidean__axioms.nCol C D A) as H3.
---- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H3.
----- exact H0.
----- destruct H3 as [H3 H4].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H5.
------ exact H4.
------ destruct H5 as [H5 H6].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H7.
------- exact H6.
------- destruct H7 as [H7 H8].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H9.
-------- exact H8.
-------- destruct H9 as [H9 H10].
apply (@lemma__rightangleNC.lemma__rightangleNC (C) (D) (A) H9).
---- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H4.
----- assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D)))))) as H4.
------ exact H0.
------ destruct H4 as [H4 H5].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D))))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D)))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (exists (X: euclidean__axioms.Point), (euclidean__axioms.BetS A X C) /\ (euclidean__axioms.BetS B X D))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
exact H11.
----- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D))) as H5.
------ exact H4.
------ destruct H5 as [M H5].
assert (* AndElim *) ((euclidean__axioms.BetS A M C) /\ (euclidean__axioms.BetS B M D)) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Per D A B) /\ ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))))) as H8.
-------- exact H0.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Per A B C) /\ ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)))) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
assert (* AndElim *) ((euclidean__defs.Per B C D) /\ ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D))) as H12.
---------- exact H11.
---------- destruct H12 as [H12 H13].
assert (* AndElim *) ((euclidean__defs.Per C D A) /\ (euclidean__defs.CR A C B D)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
assert (* Cut *) (~(euclidean__defs.Meet A B C D)) as H16.
------------ intro H16.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col C D P)))) as H17.
------------- exact H16.
------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col C D P))))) as H18.
-------------- exact H17.
-------------- destruct H18 as [P H18].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col C D P)))) as H19.
--------------- exact H18.
--------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col C D P))) as H21.
---------------- exact H20.
---------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ (euclidean__axioms.Col C D P)) as H23.
----------------- exact H22.
----------------- destruct H23 as [H23 H24].
assert (* Cut *) (~(A = P)) as H25.
------------------ intro H25.
assert (* Cut *) (euclidean__axioms.Col C D A) as H26.
------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun A0: euclidean__axioms.Point => (euclidean__defs.RE A0 B C D) -> ((euclidean__defs.Per D A0 B) -> ((euclidean__defs.Per A0 B C) -> ((euclidean__defs.Per C D A0) -> ((euclidean__defs.CR A0 C B D) -> ((euclidean__axioms.nCol D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.nCol C D A0) -> ((euclidean__axioms.BetS A0 M C) -> ((euclidean__defs.Meet A0 B C D) -> ((euclidean__axioms.neq A0 B) -> ((euclidean__axioms.Col A0 B P) -> (euclidean__axioms.Col C D A0)))))))))))))) with (x := A).
--------------------intro H26.
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
exact H24.

-------------------- exact H25.
-------------------- exact H.
-------------------- exact H8.
-------------------- exact H10.
-------------------- exact H14.
-------------------- exact H15.
-------------------- exact H1.
-------------------- exact H2.
-------------------- exact H3.
-------------------- exact H6.
-------------------- exact H16.
-------------------- exact H19.
-------------------- exact H23.
------------------- apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H3) H26).
------------------ assert (* Cut *) (~(D = P)) as H26.
------------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col A B D) as H27.
-------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun D0: euclidean__axioms.Point => (euclidean__defs.RE A B C D0) -> ((euclidean__defs.Per D0 A B) -> ((euclidean__defs.Per B C D0) -> ((euclidean__defs.Per C D0 A) -> ((euclidean__defs.CR A C B D0) -> ((euclidean__axioms.nCol D0 A B) -> ((euclidean__axioms.nCol C D0 A) -> ((euclidean__axioms.BetS B M D0) -> ((euclidean__defs.Meet A B C D0) -> ((euclidean__axioms.neq C D0) -> ((euclidean__axioms.Col C D0 P) -> (euclidean__axioms.Col A B D0))))))))))))) with (x := D).
---------------------intro H27.
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
exact H23.

--------------------- exact H26.
--------------------- exact H.
--------------------- exact H8.
--------------------- exact H12.
--------------------- exact H14.
--------------------- exact H15.
--------------------- exact H1.
--------------------- exact H3.
--------------------- exact H7.
--------------------- exact H16.
--------------------- exact H21.
--------------------- exact H24.
-------------------- assert (* Cut *) (euclidean__axioms.Col D A B) as H28.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H28.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (D) H27).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col B D A) /\ ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A)))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A))) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col A D B) /\ (euclidean__axioms.Col D B A)) as H35.
-------------------------- exact H34.
-------------------------- destruct H35 as [H35 H36].
exact H33.
--------------------- apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H3)).
----------------------apply (@euclidean__tactics.not__nCol__Col (C) (D) (A)).
-----------------------intro H29.
apply (@euclidean__tactics.Col__nCol__False (D) (A) (B) (H1) H28).


------------------- assert (* Cut *) (euclidean__defs.Per B A D) as H27.
-------------------- apply (@lemma__8__2.lemma__8__2 (D) (A) (B) H8).
-------------------- assert (* Cut *) (euclidean__axioms.Col B A P) as H28.
--------------------- assert (* Cut *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H28.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (P) H23).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)) as H35.
-------------------------- exact H34.
-------------------------- destruct H35 as [H35 H36].
exact H29.
--------------------- assert (* Cut *) (euclidean__axioms.neq P A) as H29.
---------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (P) H25).
---------------------- assert (* Cut *) (euclidean__defs.Per P A D) as H30.
----------------------- apply (@lemma__collinearright.lemma__collinearright (B) (A) (P) (D) (H27) (H28) H29).
----------------------- assert (* Cut *) (euclidean__axioms.neq P D) as H31.
------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (D) (P) H26).
------------------------ assert (* Cut *) (euclidean__defs.Per P D A) as H32.
------------------------- apply (@lemma__collinearright.lemma__collinearright (C) (D) (P) (A) (H14) (H24) H31).
------------------------- assert (* Cut *) (euclidean__defs.Per A D P) as H33.
-------------------------- apply (@lemma__8__2.lemma__8__2 (P) (D) (A) H32).
-------------------------- assert (* Cut *) (~(euclidean__defs.Per P A D)) as H34.
--------------------------- apply (@lemma__8__7.lemma__8__7 (P) (D) (A) H33).
--------------------------- apply (@H34 H30).
------------ assert (* Cut *) (euclidean__axioms.neq A B) as H17.
------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H17.
-------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H2).
-------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H18.
--------------- exact H17.
--------------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H20.
---------------- exact H19.
---------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H22.
----------------- exact H21.
----------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H24.
------------------ exact H23.
------------------ destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H26.
------------------- exact H25.
------------------- destruct H26 as [H26 H27].
exact H18.
------------- assert (* Cut *) (euclidean__axioms.neq C D) as H18.
-------------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H18.
--------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (D) (A) H3).
--------------- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H19.
---------------- exact H18.
---------------- destruct H19 as [H19 H20].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))))) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))) as H23.
------------------ exact H22.
------------------ destruct H23 as [H23 H24].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))) as H25.
------------------- exact H24.
------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)) as H27.
-------------------- exact H26.
-------------------- destruct H27 as [H27 H28].
exact H19.
-------------- assert (* Cut *) (euclidean__axioms.neq D C) as H19.
--------------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H19.
---------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (D) (A) H3).
---------------- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H20.
----------------- exact H19.
----------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))))) as H22.
------------------ exact H21.
------------------ destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))) as H24.
------------------- exact H23.
------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))) as H26.
-------------------- exact H25.
-------------------- destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)) as H28.
--------------------- exact H27.
--------------------- destruct H28 as [H28 H29].
exact H26.
--------------- assert (* Cut *) (A = A) as H20.
---------------- apply (@logic.eq__refl (Point) A).
---------------- assert (* Cut *) (euclidean__axioms.Col A B A) as H21.
----------------- right.
left.
exact H20.
----------------- assert (* Cut *) (B = B) as H22.
------------------ apply (@logic.eq__refl (Point) B).
------------------ assert (* Cut *) (euclidean__axioms.Col A B B) as H23.
------------------- right.
right.
left.
exact H22.
------------------- assert (* Cut *) (C = C) as H24.
-------------------- apply (@logic.eq__refl (Point) C).
-------------------- assert (* Cut *) (euclidean__axioms.Col C D C) as H25.
--------------------- right.
left.
exact H24.
--------------------- assert (* Cut *) (D = D) as H26.
---------------------- apply (@logic.eq__refl (Point) D).
---------------------- assert (* Cut *) (euclidean__axioms.Col C D D) as H27.
----------------------- right.
right.
left.
exact H26.
----------------------- assert (* Cut *) (euclidean__axioms.BetS D M B) as H28.
------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (B) (M) (D) H7).
------------------------ assert (* Cut *) (euclidean__defs.Par A B C D) as H29.
------------------------- exists A.
exists B.
exists D.
exists C.
exists M.
split.
-------------------------- exact H17.
-------------------------- split.
--------------------------- exact H18.
--------------------------- split.
---------------------------- exact H21.
---------------------------- split.
----------------------------- exact H23.
----------------------------- split.
------------------------------ exact H17.
------------------------------ split.
------------------------------- exact H27.
------------------------------- split.
-------------------------------- exact H25.
-------------------------------- split.
--------------------------------- exact H19.
--------------------------------- split.
---------------------------------- exact H16.
---------------------------------- split.
----------------------------------- exact H6.
----------------------------------- exact H28.
------------------------- assert (* Cut *) (~(euclidean__defs.Meet A D B C)) as H30.
-------------------------- intro H30.
assert (* Cut *) (exists (P: euclidean__axioms.Point), (euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D P) /\ (euclidean__axioms.Col B C P)))) as H31.
--------------------------- exact H30.
--------------------------- assert (exists P: euclidean__axioms.Point, ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D P) /\ (euclidean__axioms.Col B C P))))) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [P H32].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D P) /\ (euclidean__axioms.Col B C P)))) as H33.
----------------------------- exact H32.
----------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.Col A D P) /\ (euclidean__axioms.Col B C P))) as H35.
------------------------------ exact H34.
------------------------------ destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A D P) /\ (euclidean__axioms.Col B C P)) as H37.
------------------------------- exact H36.
------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) (~(A = P)) as H39.
-------------------------------- intro H39.
assert (* Cut *) (euclidean__axioms.Col B C A) as H40.
--------------------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun A0: euclidean__axioms.Point => (euclidean__defs.RE A0 B C D) -> ((euclidean__defs.Per D A0 B) -> ((euclidean__defs.Per A0 B C) -> ((euclidean__defs.Per C D A0) -> ((euclidean__defs.CR A0 C B D) -> ((euclidean__axioms.nCol D A0 B) -> ((euclidean__axioms.nCol A0 B C) -> ((euclidean__axioms.nCol C D A0) -> ((euclidean__axioms.BetS A0 M C) -> ((~(euclidean__defs.Meet A0 B C D)) -> ((euclidean__axioms.neq A0 B) -> ((A0 = A0) -> ((euclidean__axioms.Col A0 B A0) -> ((euclidean__axioms.Col A0 B B) -> ((euclidean__defs.Par A0 B C D) -> ((euclidean__defs.Meet A0 D B C) -> ((euclidean__axioms.neq A0 D) -> ((euclidean__axioms.Col A0 D P) -> (euclidean__axioms.Col B C A0)))))))))))))))))))) with (x := A).
----------------------------------intro H40.
intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
exact H38.

---------------------------------- exact H39.
---------------------------------- exact H.
---------------------------------- exact H8.
---------------------------------- exact H10.
---------------------------------- exact H14.
---------------------------------- exact H15.
---------------------------------- exact H1.
---------------------------------- exact H2.
---------------------------------- exact H3.
---------------------------------- exact H6.
---------------------------------- exact H16.
---------------------------------- exact H17.
---------------------------------- exact H20.
---------------------------------- exact H21.
---------------------------------- exact H23.
---------------------------------- exact H29.
---------------------------------- exact H30.
---------------------------------- exact H33.
---------------------------------- exact H37.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col A B C) as H41.
---------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H41.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (A) H40).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B A) /\ ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col C A B) /\ ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col A B C) /\ ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B))) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col B A C) /\ (euclidean__axioms.Col A C B)) as H48.
--------------------------------------- exact H47.
--------------------------------------- destruct H48 as [H48 H49].
exact H46.
---------------------------------- apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H3)).
-----------------------------------apply (@euclidean__tactics.not__nCol__Col (C) (D) (A)).
------------------------------------intro H42.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (C) (H2) H41).


-------------------------------- assert (* Cut *) (~(B = P)) as H40.
--------------------------------- intro H40.
assert (* Cut *) (euclidean__axioms.Col A D B) as H41.
---------------------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun B0: euclidean__axioms.Point => (euclidean__defs.RE A B0 C D) -> ((euclidean__defs.Per D A B0) -> ((euclidean__defs.Per A B0 C) -> ((euclidean__defs.Per B0 C D) -> ((euclidean__defs.CR A C B0 D) -> ((euclidean__axioms.nCol D A B0) -> ((euclidean__axioms.nCol A B0 C) -> ((euclidean__axioms.BetS B0 M D) -> ((~(euclidean__defs.Meet A B0 C D)) -> ((euclidean__axioms.neq A B0) -> ((euclidean__axioms.Col A B0 A) -> ((B0 = B0) -> ((euclidean__axioms.Col A B0 B0) -> ((euclidean__axioms.BetS D M B0) -> ((euclidean__defs.Par A B0 C D) -> ((euclidean__defs.Meet A D B0 C) -> ((euclidean__axioms.neq B0 C) -> ((euclidean__axioms.Col B0 C P) -> (euclidean__axioms.Col A D B0)))))))))))))))))))) with (x := B).
-----------------------------------intro H41.
intro H42.
intro H43.
intro H44.
intro H45.
intro H46.
intro H47.
intro H48.
intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
exact H37.

----------------------------------- exact H40.
----------------------------------- exact H.
----------------------------------- exact H8.
----------------------------------- exact H10.
----------------------------------- exact H12.
----------------------------------- exact H15.
----------------------------------- exact H1.
----------------------------------- exact H2.
----------------------------------- exact H7.
----------------------------------- exact H16.
----------------------------------- exact H17.
----------------------------------- exact H21.
----------------------------------- exact H22.
----------------------------------- exact H23.
----------------------------------- exact H28.
----------------------------------- exact H29.
----------------------------------- exact H30.
----------------------------------- exact H35.
----------------------------------- exact H38.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col D A B) as H42.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))))) as H42.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (B) H41).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D A B) /\ ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col D B A) /\ ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A)))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col B A D) /\ ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A))) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A B D) /\ (euclidean__axioms.Col B D A)) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
exact H43.
----------------------------------- apply (@euclidean__tactics.Col__nCol__False (C) (D) (A) (H3)).
------------------------------------apply (@euclidean__tactics.not__nCol__Col (C) (D) (A)).
-------------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (D) (A) (B) (H1) H42).


--------------------------------- assert (* Cut *) (euclidean__axioms.neq P A) as H41.
---------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (A) (P) H39).
---------------------------------- assert (* Cut *) (euclidean__axioms.Col D A P) as H42.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col D A P) /\ ((euclidean__axioms.Col D P A) /\ ((euclidean__axioms.Col P A D) /\ ((euclidean__axioms.Col A P D) /\ (euclidean__axioms.Col P D A))))) as H42.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (A) (D) (P) H37).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col D A P) /\ ((euclidean__axioms.Col D P A) /\ ((euclidean__axioms.Col P A D) /\ ((euclidean__axioms.Col A P D) /\ (euclidean__axioms.Col P D A))))) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col D P A) /\ ((euclidean__axioms.Col P A D) /\ ((euclidean__axioms.Col A P D) /\ (euclidean__axioms.Col P D A)))) as H45.
-------------------------------------- exact H44.
-------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col P A D) /\ ((euclidean__axioms.Col A P D) /\ (euclidean__axioms.Col P D A))) as H47.
--------------------------------------- exact H46.
--------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A P D) /\ (euclidean__axioms.Col P D A)) as H49.
---------------------------------------- exact H48.
---------------------------------------- destruct H49 as [H49 H50].
exact H43.
----------------------------------- assert (* Cut *) (euclidean__defs.Per P A B) as H43.
------------------------------------ apply (@lemma__collinearright.lemma__collinearright (D) (A) (P) (B) (H8) (H42) H41).
------------------------------------ assert (* Cut *) (euclidean__defs.Per C B A) as H44.
------------------------------------- apply (@lemma__8__2.lemma__8__2 (A) (B) (C) H10).
------------------------------------- assert (* Cut *) (euclidean__axioms.Col C B P) as H45.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col C P B) /\ ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B P C) /\ (euclidean__axioms.Col P C B))))) as H45.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (C) (P) H38).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col C B P) /\ ((euclidean__axioms.Col C P B) /\ ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B P C) /\ (euclidean__axioms.Col P C B))))) as H46.
---------------------------------------- exact H45.
---------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col C P B) /\ ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B P C) /\ (euclidean__axioms.Col P C B)))) as H48.
----------------------------------------- exact H47.
----------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col P B C) /\ ((euclidean__axioms.Col B P C) /\ (euclidean__axioms.Col P C B))) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [H50 H51].
assert (* AndElim *) ((euclidean__axioms.Col B P C) /\ (euclidean__axioms.Col P C B)) as H52.
------------------------------------------- exact H51.
------------------------------------------- destruct H52 as [H52 H53].
exact H46.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq P B) as H46.
--------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (P) H40).
--------------------------------------- assert (* Cut *) (euclidean__defs.Per P B A) as H47.
---------------------------------------- apply (@lemma__collinearright.lemma__collinearright (C) (B) (P) (A) (H44) (H45) H46).
---------------------------------------- assert (* Cut *) (euclidean__defs.Per B A P) as H48.
----------------------------------------- apply (@lemma__8__2.lemma__8__2 (P) (A) (B) H43).
----------------------------------------- assert (* Cut *) (~(euclidean__defs.Per P B A)) as H49.
------------------------------------------ apply (@lemma__8__7.lemma__8__7 (P) (A) (B) H48).
------------------------------------------ apply (@H49 H47).
-------------------------- assert (* Cut *) (euclidean__axioms.neq A D) as H31.
--------------------------- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H31.
---------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (C) (D) (A) H3).
---------------------------- assert (* AndElim *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))))) as H32.
----------------------------- exact H31.
----------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq D A) /\ ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))))) as H34.
------------------------------ exact H33.
------------------------------ destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.neq C A) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)))) as H36.
------------------------------- exact H35.
------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq A D) /\ (euclidean__axioms.neq A C)) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
exact H40.
--------------------------- assert (* Cut *) (euclidean__axioms.neq B C) as H32.
---------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H32.
----------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct (A) (B) (C) H2).
----------------------------- assert (* AndElim *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))))) as H33.
------------------------------ exact H32.
------------------------------ destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))))) as H35.
------------------------------- exact H34.
------------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)))) as H37.
-------------------------------- exact H36.
-------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A))) as H39.
--------------------------------- exact H38.
--------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C A)) as H41.
---------------------------------- exact H40.
---------------------------------- destruct H41 as [H41 H42].
exact H35.
---------------------------- assert (* Cut *) (D = D) as H33.
----------------------------- exact H26.
----------------------------- assert (* Cut *) (euclidean__axioms.Col A D A) as H34.
------------------------------ right.
left.
exact H20.
------------------------------ assert (* Cut *) (euclidean__axioms.Col A D D) as H35.
------------------------------- right.
right.
left.
exact H33.
------------------------------- assert (* Cut *) (euclidean__axioms.Col B C B) as H36.
-------------------------------- right.
left.
exact H22.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col B C C) as H37.
--------------------------------- right.
right.
left.
exact H24.
--------------------------------- assert (* Cut *) (euclidean__defs.Par A D B C) as H38.
---------------------------------- exists A.
exists D.
exists B.
exists C.
exists M.
split.
----------------------------------- exact H31.
----------------------------------- split.
------------------------------------ exact H32.
------------------------------------ split.
------------------------------------- exact H34.
------------------------------------- split.
-------------------------------------- exact H35.
-------------------------------------- split.
--------------------------------------- exact H31.
--------------------------------------- split.
---------------------------------------- exact H36.
---------------------------------------- split.
----------------------------------------- exact H37.
----------------------------------------- split.
------------------------------------------ exact H32.
------------------------------------------ split.
------------------------------------------- exact H30.
------------------------------------------- split.
-------------------------------------------- exact H6.
-------------------------------------------- exact H7.
---------------------------------- assert (* Cut *) (euclidean__defs.PG A B C D) as H39.
----------------------------------- split.
------------------------------------ exact H29.
------------------------------------ exact H38.
----------------------------------- exact H39.
Qed.
