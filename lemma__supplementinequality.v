Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__ABCequalsCBA.
Require Export lemma__angleorderrespectscongruence.
Require Export lemma__angleorderrespectscongruence2.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__equalanglesNC.
Require Export lemma__equalanglesflip.
Require Export lemma__equalangleshelper.
Require Export lemma__equalanglesreflexive.
Require Export lemma__equalanglessymmetric.
Require Export lemma__equalanglestransitive.
Require Export lemma__inequalitysymmetric.
Require Export lemma__ray1.
Require Export lemma__ray3.
Require Export lemma__ray4.
Require Export lemma__ray5.
Require Export lemma__rayimpliescollinear.
Require Export lemma__raystrict.
Require Export lemma__supplements.
Require Export logic.
Definition lemma__supplementinequality : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (F: euclidean__axioms.Point) (a: euclidean__axioms.Point) (b: euclidean__axioms.Point) (c: euclidean__axioms.Point) (d: euclidean__axioms.Point) (f: euclidean__axioms.Point), (euclidean__defs.Supp A B C D F) -> ((euclidean__defs.Supp a b c d f) -> ((euclidean__defs.LtA a b c A B C) -> (euclidean__defs.LtA D B F d b f))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro F.
intro a.
intro b.
intro c.
intro d.
intro f.
intro H.
intro H0.
intro H1.
assert (* Cut *) (exists (P: euclidean__axioms.Point) (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.BetS P R Q) /\ ((euclidean__defs.Out B A P) /\ ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R)))) as H2.
- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ (euclidean__defs.CongA a b c A B X)))) as H2.
-- exact H1.
-- assert (* Cut *) (exists (U: euclidean__axioms.Point) (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ (euclidean__defs.CongA a b c A B X)))) as __TmpHyp.
--- exact H2.
--- assert (exists U: euclidean__axioms.Point, (exists (X: euclidean__axioms.Point) (V: euclidean__axioms.Point), (euclidean__axioms.BetS U X V) /\ ((euclidean__defs.Out B A U) /\ ((euclidean__defs.Out B C V) /\ (euclidean__defs.CongA a b c A B X))))) as H3.
---- exact __TmpHyp.
---- destruct H3 as [x H3].
assert (exists X: euclidean__axioms.Point, (exists (V: euclidean__axioms.Point), (euclidean__axioms.BetS x X V) /\ ((euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C V) /\ (euclidean__defs.CongA a b c A B X))))) as H4.
----- exact H3.
----- destruct H4 as [x0 H4].
assert (exists V: euclidean__axioms.Point, ((euclidean__axioms.BetS x x0 V) /\ ((euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C V) /\ (euclidean__defs.CongA a b c A B x0))))) as H5.
------ exact H4.
------ destruct H5 as [x1 H5].
assert (* AndElim *) ((euclidean__axioms.BetS x x0 x1) /\ ((euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C x1) /\ (euclidean__defs.CongA a b c A B x0)))) as H6.
------- exact H5.
------- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Out B A x) /\ ((euclidean__defs.Out B C x1) /\ (euclidean__defs.CongA a b c A B x0))) as H8.
-------- exact H7.
-------- destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Out B C x1) /\ (euclidean__defs.CongA a b c A B x0)) as H10.
--------- exact H9.
--------- destruct H10 as [H10 H11].
exists x.
exists x1.
exists x0.
split.
---------- exact H6.
---------- split.
----------- exact H8.
----------- split.
------------ exact H10.
------------ exact H11.
- assert (exists P: euclidean__axioms.Point, (exists (Q: euclidean__axioms.Point) (R: euclidean__axioms.Point), (euclidean__axioms.BetS P R Q) /\ ((euclidean__defs.Out B A P) /\ ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R))))) as H3.
-- exact H2.
-- destruct H3 as [P H3].
assert (exists Q: euclidean__axioms.Point, (exists (R: euclidean__axioms.Point), (euclidean__axioms.BetS P R Q) /\ ((euclidean__defs.Out B A P) /\ ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R))))) as H4.
--- exact H3.
--- destruct H4 as [Q H4].
assert (exists R: euclidean__axioms.Point, ((euclidean__axioms.BetS P R Q) /\ ((euclidean__defs.Out B A P) /\ ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R))))) as H5.
---- exact H4.
---- destruct H5 as [R H5].
assert (* AndElim *) ((euclidean__axioms.BetS P R Q) /\ ((euclidean__defs.Out B A P) /\ ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R)))) as H6.
----- exact H5.
----- destruct H6 as [H6 H7].
assert (* AndElim *) ((euclidean__defs.Out B A P) /\ ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R))) as H8.
------ exact H7.
------ destruct H8 as [H8 H9].
assert (* AndElim *) ((euclidean__defs.Out B C Q) /\ (euclidean__defs.CongA a b c A B R)) as H10.
------- exact H9.
------- destruct H10 as [H10 H11].
assert (* Cut *) (euclidean__axioms.nCol A B R) as H12.
-------- apply (@euclidean__tactics.nCol__notCol (A) (B) (R)).
---------apply (@euclidean__tactics.nCol__not__Col (A) (B) (R)).
----------apply (@lemma__equalanglesNC.lemma__equalanglesNC (a) (b) (c) (A) (B) (R) H11).


-------- assert (* Cut *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H13.
--------- assert (* Cut *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as H13.
---------- exact H0.
---------- assert (* Cut *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as __TmpHyp.
----------- exact H13.
----------- assert (* AndElim *) ((euclidean__defs.Out b c d) /\ (euclidean__axioms.BetS a b f)) as H14.
------------ exact __TmpHyp.
------------ destruct H14 as [H14 H15].
assert (* Cut *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H16.
------------- exact H.
------------- assert (* Cut *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as __TmpHyp0.
-------------- exact H16.
-------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H17.
--------------- exact __TmpHyp0.
--------------- destruct H17 as [H17 H18].
split.
---------------- exact H17.
---------------- exact H18.
--------- assert (* Cut *) (euclidean__axioms.BetS Q R P) as H14.
---------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H14.
----------- exact H13.
----------- destruct H14 as [H14 H15].
apply (@euclidean__axioms.axiom__betweennesssymmetry (P) (R) (Q) H6).
---------- assert (* Cut *) (euclidean__axioms.BetS F B A) as H15.
----------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H15.
------------ exact H13.
------------ destruct H15 as [H15 H16].
apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (B) (F) H16).
----------- assert (* Cut *) ((euclidean__axioms.BetS B P A) \/ ((A = P) \/ (euclidean__axioms.BetS B A P))) as H16.
------------ assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H16.
------------- exact H13.
------------- destruct H16 as [H16 H17].
apply (@lemma__ray1.lemma__ray1 (B) (A) (P) H8).
------------ assert (* Cut *) (euclidean__axioms.BetS F B P) as H17.
------------- assert (* Cut *) ((euclidean__axioms.BetS B P A) \/ ((A = P) \/ (euclidean__axioms.BetS B A P))) as H17.
-------------- exact H16.
-------------- assert (* Cut *) ((euclidean__axioms.BetS B P A) \/ ((A = P) \/ (euclidean__axioms.BetS B A P))) as __TmpHyp.
--------------- exact H17.
--------------- assert (euclidean__axioms.BetS B P A \/ (A = P) \/ (euclidean__axioms.BetS B A P)) as H18.
---------------- exact __TmpHyp.
---------------- destruct H18 as [H18|H18].
----------------- assert (* Cut *) (euclidean__axioms.BetS F B P) as H19.
------------------ assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H19.
------------------- exact H13.
------------------- destruct H19 as [H19 H20].
apply (@euclidean__axioms.axiom__innertransitivity (F) (B) (P) (A) (H15) H18).
------------------ exact H19.
----------------- assert (A = P \/ euclidean__axioms.BetS B A P) as H19.
------------------ exact H18.
------------------ destruct H19 as [H19|H19].
------------------- assert (* Cut *) (euclidean__axioms.BetS F B P) as H20.
-------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H20.
--------------------- exact H13.
--------------------- destruct H20 as [H20 H21].
apply (@eq__ind__r euclidean__axioms.Point P (fun A0: euclidean__axioms.Point => (euclidean__defs.Supp A0 B C D F) -> ((euclidean__defs.LtA a b c A0 B C) -> ((euclidean__defs.Out B A0 P) -> ((euclidean__defs.CongA a b c A0 B R) -> ((euclidean__axioms.nCol A0 B R) -> ((euclidean__axioms.BetS A0 B F) -> ((euclidean__axioms.BetS F B A0) -> (euclidean__axioms.BetS F B P))))))))) with (x := A).
----------------------intro H22.
intro H23.
intro H24.
intro H25.
intro H26.
intro H27.
intro H28.
exact H28.

---------------------- exact H19.
---------------------- exact H.
---------------------- exact H1.
---------------------- exact H8.
---------------------- exact H11.
---------------------- exact H12.
---------------------- exact H21.
---------------------- exact H15.
-------------------- exact H20.
------------------- assert (* Cut *) (euclidean__axioms.BetS F B P) as H20.
-------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H20.
--------------------- exact H13.
--------------------- destruct H20 as [H20 H21].
apply (@lemma__3__7b.lemma__3__7b (F) (B) (A) (P) (H15) H19).
-------------------- exact H20.
------------- assert (* Cut *) (~(euclidean__axioms.Col F P Q)) as H18.
-------------- intro H18.
assert (* Cut *) (euclidean__axioms.Col B A P) as H19.
--------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H19.
---------------- exact H13.
---------------- destruct H19 as [H19 H20].
apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (A) (P) H8).
--------------- assert (* Cut *) (euclidean__axioms.Col A B F) as H20.
---------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H20.
----------------- exact H13.
----------------- destruct H20 as [H20 H21].
assert (euclidean__axioms.BetS B P A \/ (A = P) \/ (euclidean__axioms.BetS B A P)) as H22.
------------------ exact H16.
------------------ destruct H22 as [H22|H22].
------------------- right.
right.
right.
right.
left.
exact H21.
------------------- assert (A = P \/ euclidean__axioms.BetS B A P) as H23.
-------------------- exact H22.
-------------------- destruct H23 as [H23|H23].
--------------------- right.
right.
right.
right.
left.
exact H21.
--------------------- right.
right.
right.
right.
left.
exact H21.
---------------- assert (* Cut *) (euclidean__axioms.neq A B) as H21.
----------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H21.
------------------ exact H13.
------------------ destruct H21 as [H21 H22].
assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H23.
------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (F) H22).
------------------- assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H24.
-------------------- exact H23.
-------------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F)) as H26.
--------------------- exact H25.
--------------------- destruct H26 as [H26 H27].
exact H26.
----------------- assert (* Cut *) (euclidean__axioms.Col A B P) as H22.
------------------ assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H22.
------------------- exact H13.
------------------- destruct H22 as [H22 H23].
assert (* Cut *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H24.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (A) (P) H19).
-------------------- assert (* AndElim *) ((euclidean__axioms.Col A B P) /\ ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))))) as H25.
--------------------- exact H24.
--------------------- destruct H25 as [H25 H26].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B)))) as H27.
---------------------- exact H26.
---------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col P B A) /\ ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ (euclidean__axioms.Col P A B)) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
exact H25.
------------------ assert (* Cut *) (euclidean__axioms.Col B F P) as H23.
------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H23.
-------------------- exact H13.
-------------------- destruct H23 as [H23 H24].
apply (@euclidean__tactics.not__nCol__Col (B) (F) (P)).
---------------------intro H25.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (P) (H25)).
----------------------apply (@lemma__collinear4.lemma__collinear4 (A) (B) (F) (P) (H20) (H22) H21).


------------------- assert (* Cut *) (euclidean__axioms.Col F P B) as H24.
-------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H24.
--------------------- exact H13.
--------------------- destruct H24 as [H24 H25].
assert (* Cut *) ((euclidean__axioms.Col F B P) /\ ((euclidean__axioms.Col F P B) /\ ((euclidean__axioms.Col P B F) /\ ((euclidean__axioms.Col B P F) /\ (euclidean__axioms.Col P F B))))) as H26.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (P) H23).
---------------------- assert (* AndElim *) ((euclidean__axioms.Col F B P) /\ ((euclidean__axioms.Col F P B) /\ ((euclidean__axioms.Col P B F) /\ ((euclidean__axioms.Col B P F) /\ (euclidean__axioms.Col P F B))))) as H27.
----------------------- exact H26.
----------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.Col F P B) /\ ((euclidean__axioms.Col P B F) /\ ((euclidean__axioms.Col B P F) /\ (euclidean__axioms.Col P F B)))) as H29.
------------------------ exact H28.
------------------------ destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.Col P B F) /\ ((euclidean__axioms.Col B P F) /\ (euclidean__axioms.Col P F B))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B P F) /\ (euclidean__axioms.Col P F B)) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
exact H29.
-------------------- assert (* Cut *) (euclidean__axioms.neq F P) as H25.
--------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H25.
---------------------- exact H13.
---------------------- destruct H25 as [H25 H26].
assert (* Cut *) ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F P))) as H27.
----------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (B) (P) H17).
----------------------- assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F P))) as H28.
------------------------ exact H27.
------------------------ destruct H28 as [H28 H29].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F P)) as H30.
------------------------- exact H29.
------------------------- destruct H30 as [H30 H31].
exact H31.
--------------------- assert (* Cut *) (euclidean__axioms.Col P Q B) as H26.
---------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H26.
----------------------- exact H13.
----------------------- destruct H26 as [H26 H27].
apply (@euclidean__tactics.not__nCol__Col (P) (Q) (B)).
------------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (P) (Q) (B) (H28)).
-------------------------apply (@lemma__collinear4.lemma__collinear4 (F) (P) (Q) (B) (H18) (H24) H25).


---------------------- assert (* Cut *) (euclidean__axioms.Col P B Q) as H27.
----------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H27.
------------------------ exact H13.
------------------------ destruct H27 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P))))) as H29.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (Q) (B) H26).
------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P))))) as H30.
-------------------------- exact H29.
-------------------------- destruct H30 as [H30 H31].
assert (* AndElim *) ((euclidean__axioms.Col Q B P) /\ ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P)))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P))) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
assert (* AndElim *) ((euclidean__axioms.Col P B Q) /\ (euclidean__axioms.Col B Q P)) as H36.
----------------------------- exact H35.
----------------------------- destruct H36 as [H36 H37].
exact H36.
----------------------- assert (* Cut *) (euclidean__axioms.Col P B A) as H28.
------------------------ assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H28.
------------------------- exact H13.
------------------------- destruct H28 as [H28 H29].
assert (* Cut *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H30.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder (A) (B) (P) H22).
-------------------------- assert (* AndElim *) ((euclidean__axioms.Col B A P) /\ ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))))) as H31.
--------------------------- exact H30.
--------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.Col B P A) /\ ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)))) as H33.
---------------------------- exact H32.
---------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.Col P A B) /\ ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A))) as H35.
----------------------------- exact H34.
----------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.Col A P B) /\ (euclidean__axioms.Col P B A)) as H37.
------------------------------ exact H36.
------------------------------ destruct H37 as [H37 H38].
exact H38.
------------------------ assert (* Cut *) (euclidean__axioms.neq B P) as H29.
------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H29.
-------------------------- exact H13.
-------------------------- destruct H29 as [H29 H30].
assert (* Cut *) ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F P))) as H31.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (B) (P) H17).
--------------------------- assert (* AndElim *) ((euclidean__axioms.neq B P) /\ ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F P))) as H32.
---------------------------- exact H31.
---------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq F B) /\ (euclidean__axioms.neq F P)) as H34.
----------------------------- exact H33.
----------------------------- destruct H34 as [H34 H35].
exact H32.
------------------------- assert (* Cut *) (euclidean__axioms.neq P B) as H30.
-------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H30.
--------------------------- exact H13.
--------------------------- destruct H30 as [H30 H31].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (P) H29).
-------------------------- assert (* Cut *) (euclidean__axioms.Col B Q A) as H31.
--------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H31.
---------------------------- exact H13.
---------------------------- destruct H31 as [H31 H32].
apply (@euclidean__tactics.not__nCol__Col (B) (Q) (A)).
-----------------------------intro H33.
apply (@euclidean__tactics.Col__nCol__False (B) (Q) (A) (H33)).
------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (B) (Q) (A) (H27) (H28) H30).


--------------------------- assert (* Cut *) (euclidean__axioms.Col P R Q) as H32.
---------------------------- right.
right.
right.
right.
left.
exact H6.
---------------------------- assert (* Cut *) (euclidean__axioms.Col P Q R) as H33.
----------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H33.
------------------------------ exact H13.
------------------------------ destruct H33 as [H33 H34].
assert (* Cut *) ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col R Q P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P))))) as H35.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (R) (Q) H32).
------------------------------- assert (* AndElim *) ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col R Q P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P))))) as H36.
-------------------------------- exact H35.
-------------------------------- destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.Col R Q P) /\ ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P)))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col P Q R) /\ (euclidean__axioms.Col Q R P)) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
exact H42.
----------------------------- assert (* Cut *) (euclidean__axioms.Col P Q B) as H34.
------------------------------ assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H34.
------------------------------- exact H13.
------------------------------- destruct H34 as [H34 H35].
assert (* Cut *) ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col Q R P) /\ ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col P R Q) /\ (euclidean__axioms.Col R Q P))))) as H36.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (P) (Q) (R) H33).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q P R) /\ ((euclidean__axioms.Col Q R P) /\ ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col P R Q) /\ (euclidean__axioms.Col R Q P))))) as H37.
--------------------------------- exact H36.
--------------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.Col Q R P) /\ ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col P R Q) /\ (euclidean__axioms.Col R Q P)))) as H39.
---------------------------------- exact H38.
---------------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.Col R P Q) /\ ((euclidean__axioms.Col P R Q) /\ (euclidean__axioms.Col R Q P))) as H41.
----------------------------------- exact H40.
----------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col P R Q) /\ (euclidean__axioms.Col R Q P)) as H43.
------------------------------------ exact H42.
------------------------------------ destruct H43 as [H43 H44].
exact H26.
------------------------------ assert (* Cut *) (euclidean__axioms.neq P Q) as H35.
------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H35.
-------------------------------- exact H13.
-------------------------------- destruct H35 as [H35 H36].
assert (* Cut *) ((euclidean__axioms.neq R Q) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q))) as H37.
--------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (P) (R) (Q) H6).
--------------------------------- assert (* AndElim *) ((euclidean__axioms.neq R Q) /\ ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q))) as H38.
---------------------------------- exact H37.
---------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.neq P R) /\ (euclidean__axioms.neq P Q)) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
exact H41.
------------------------------- assert (* Cut *) (euclidean__axioms.Col Q R B) as H36.
-------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H36.
--------------------------------- exact H13.
--------------------------------- destruct H36 as [H36 H37].
apply (@euclidean__tactics.not__nCol__Col (Q) (R) (B)).
----------------------------------intro H38.
apply (@euclidean__tactics.Col__nCol__False (Q) (R) (B) (H38)).
-----------------------------------apply (@lemma__collinear4.lemma__collinear4 (P) (Q) (R) (B) (H33) (H34) H35).


-------------------------------- assert (* Cut *) (euclidean__axioms.Col Q B R) as H37.
--------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H37.
---------------------------------- exact H13.
---------------------------------- destruct H37 as [H37 H38].
assert (* Cut *) ((euclidean__axioms.Col R Q B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B Q R) /\ ((euclidean__axioms.Col Q B R) /\ (euclidean__axioms.Col B R Q))))) as H39.
----------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (R) (B) H36).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.Col R Q B) /\ ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B Q R) /\ ((euclidean__axioms.Col Q B R) /\ (euclidean__axioms.Col B R Q))))) as H40.
------------------------------------ exact H39.
------------------------------------ destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col R B Q) /\ ((euclidean__axioms.Col B Q R) /\ ((euclidean__axioms.Col Q B R) /\ (euclidean__axioms.Col B R Q)))) as H42.
------------------------------------- exact H41.
------------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col B Q R) /\ ((euclidean__axioms.Col Q B R) /\ (euclidean__axioms.Col B R Q))) as H44.
-------------------------------------- exact H43.
-------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col Q B R) /\ (euclidean__axioms.Col B R Q)) as H46.
--------------------------------------- exact H45.
--------------------------------------- destruct H46 as [H46 H47].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.Col Q B A) as H38.
---------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H38.
----------------------------------- exact H13.
----------------------------------- destruct H38 as [H38 H39].
assert (* Cut *) ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B A Q) /\ (euclidean__axioms.Col A Q B))))) as H40.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (B) (Q) (A) H31).
------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col Q B A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B A Q) /\ (euclidean__axioms.Col A Q B))))) as H41.
------------------------------------- exact H40.
------------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B A Q) /\ (euclidean__axioms.Col A Q B)))) as H43.
-------------------------------------- exact H42.
-------------------------------------- destruct H43 as [H43 H44].
assert (* AndElim *) ((euclidean__axioms.Col A B Q) /\ ((euclidean__axioms.Col B A Q) /\ (euclidean__axioms.Col A Q B))) as H45.
--------------------------------------- exact H44.
--------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col B A Q) /\ (euclidean__axioms.Col A Q B)) as H47.
---------------------------------------- exact H46.
---------------------------------------- destruct H47 as [H47 H48].
exact H41.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H39.
----------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H39.
------------------------------------ exact H13.
------------------------------------ destruct H39 as [H39 H40].
apply (@lemma__raystrict.lemma__raystrict (B) (C) (Q) H10).
----------------------------------- assert (* Cut *) (euclidean__axioms.neq Q B) as H40.
------------------------------------ assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H40.
------------------------------------- exact H13.
------------------------------------- destruct H40 as [H40 H41].
apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (Q) H39).
------------------------------------ assert (* Cut *) (euclidean__axioms.Col B R A) as H41.
------------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H41.
-------------------------------------- exact H13.
-------------------------------------- destruct H41 as [H41 H42].
apply (@euclidean__tactics.not__nCol__Col (B) (R) (A)).
---------------------------------------intro H43.
apply (@euclidean__tactics.Col__nCol__False (B) (R) (A) (H43)).
----------------------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (B) (R) (A) (H37) (H38) H40).


------------------------------------- assert (* Cut *) (euclidean__axioms.Col A B R) as H42.
-------------------------------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H42.
--------------------------------------- exact H13.
--------------------------------------- destruct H42 as [H42 H43].
assert (* Cut *) ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.Col A R B))))) as H44.
---------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (R) (A) H41).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.Col A R B))))) as H45.
----------------------------------------- exact H44.
----------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.Col A R B)))) as H47.
------------------------------------------ exact H46.
------------------------------------------ destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.Col A R B))) as H49.
------------------------------------------- exact H48.
------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.Col A R B)) as H51.
-------------------------------------------- exact H50.
-------------------------------------------- destruct H51 as [H51 H52].
exact H49.
-------------------------------------- apply (@euclidean__tactics.Col__nCol__False (A) (B) (R) (H12) H42).
-------------- assert (* Cut *) (exists (M: euclidean__axioms.Point), (euclidean__axioms.BetS F M R) /\ (euclidean__axioms.BetS Q M B)) as H19.
--------------- assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H19.
---------------- exact H13.
---------------- destruct H19 as [H19 H20].
apply (@euclidean__axioms.postulate__Pasch__inner (F) (Q) (P) (B) (R) (H17) (H14)).
-----------------apply (@euclidean__tactics.nCol__notCol (F) (P) (Q) H18).

--------------- assert (exists M: euclidean__axioms.Point, ((euclidean__axioms.BetS F M R) /\ (euclidean__axioms.BetS Q M B))) as H20.
---------------- exact H19.
---------------- destruct H20 as [M H20].
assert (* AndElim *) ((euclidean__axioms.BetS F M R) /\ (euclidean__axioms.BetS Q M B)) as H21.
----------------- exact H20.
----------------- destruct H21 as [H21 H22].
assert (* AndElim *) ((euclidean__defs.Out B C D) /\ (euclidean__axioms.BetS A B F)) as H23.
------------------ exact H13.
------------------ destruct H23 as [H23 H24].
assert (* Cut *) (R = R) as H25.
------------------- apply (@logic.eq__refl (Point) R).
------------------- assert (* Cut *) (~(B = R)) as H26.
-------------------- intro H26.
assert (* Cut *) (euclidean__axioms.Col A B R) as H27.
--------------------- right.
right.
left.
exact H26.
--------------------- apply (@H18).
----------------------apply (@euclidean__tactics.not__nCol__Col (F) (P) (Q)).
-----------------------intro H28.
apply (@euclidean__tactics.Col__nCol__False (A) (B) (R) (H12) H27).


-------------------- assert (* Cut *) (euclidean__defs.Out B R R) as H27.
--------------------- apply (@lemma__ray4.lemma__ray4 (B) (R) (R)).
----------------------right.
left.
exact H25.

---------------------- exact H26.
--------------------- assert (* Cut *) (euclidean__defs.Supp A B R R F) as H28.
---------------------- split.
----------------------- exact H27.
----------------------- exact H24.
---------------------- assert (* Cut *) (euclidean__defs.CongA A B R a b c) as H29.
----------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (a) (b) (c) (A) (B) (R) H11).
----------------------- assert (* Cut *) (euclidean__defs.CongA R B F d b f) as H30.
------------------------ apply (@lemma__supplements.lemma__supplements (A) (B) (R) (R) (F) (a) (b) (c) (d) (f) (H29) (H28) H0).
------------------------ assert (* Cut *) (euclidean__axioms.neq B F) as H31.
------------------------- assert (* Cut *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H31.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (A) (B) (F) H24).
-------------------------- assert (* AndElim *) ((euclidean__axioms.neq B F) /\ ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F))) as H32.
--------------------------- exact H31.
--------------------------- destruct H32 as [H32 H33].
assert (* AndElim *) ((euclidean__axioms.neq A B) /\ (euclidean__axioms.neq A F)) as H34.
---------------------------- exact H33.
---------------------------- destruct H34 as [H34 H35].
exact H32.
------------------------- assert (* Cut *) (F = F) as H32.
-------------------------- apply (@logic.eq__refl (Point) F).
-------------------------- assert (* Cut *) (euclidean__defs.Out B F F) as H33.
--------------------------- apply (@lemma__ray4.lemma__ray4 (B) (F) (F)).
----------------------------right.
left.
exact H32.

---------------------------- exact H31.
--------------------------- assert (* Cut *) (euclidean__defs.CongA d b f R B F) as H34.
---------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (R) (B) (F) (d) (b) (f) H30).
---------------------------- assert (* Cut *) (euclidean__axioms.nCol R B F) as H35.
----------------------------- apply (@euclidean__tactics.nCol__notCol (R) (B) (F)).
------------------------------apply (@euclidean__tactics.nCol__not__Col (R) (B) (F)).
-------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (d) (b) (f) (R) (B) (F) H34).


----------------------------- assert (* Cut *) (~(euclidean__axioms.Col F B Q)) as H36.
------------------------------ intro H36.
assert (* Cut *) (euclidean__axioms.Col Q B F) as H37.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col B F Q) /\ ((euclidean__axioms.Col B Q F) /\ ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F Q B) /\ (euclidean__axioms.Col Q B F))))) as H37.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (B) (Q) H36).
-------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B F Q) /\ ((euclidean__axioms.Col B Q F) /\ ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F Q B) /\ (euclidean__axioms.Col Q B F))))) as H38.
--------------------------------- exact H37.
--------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.Col B Q F) /\ ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F Q B) /\ (euclidean__axioms.Col Q B F)))) as H40.
---------------------------------- exact H39.
---------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F Q B) /\ (euclidean__axioms.Col Q B F))) as H42.
----------------------------------- exact H41.
----------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col F Q B) /\ (euclidean__axioms.Col Q B F)) as H44.
------------------------------------ exact H43.
------------------------------------ destruct H44 as [H44 H45].
exact H45.
------------------------------- assert (* Cut *) (euclidean__axioms.Col Q M B) as H38.
-------------------------------- right.
right.
right.
right.
left.
exact H22.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col Q B M) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col M Q B) /\ ((euclidean__axioms.Col M B Q) /\ ((euclidean__axioms.Col B Q M) /\ ((euclidean__axioms.Col Q B M) /\ (euclidean__axioms.Col B M Q))))) as H39.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (Q) (M) (B) H38).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M Q B) /\ ((euclidean__axioms.Col M B Q) /\ ((euclidean__axioms.Col B Q M) /\ ((euclidean__axioms.Col Q B M) /\ (euclidean__axioms.Col B M Q))))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.Col M B Q) /\ ((euclidean__axioms.Col B Q M) /\ ((euclidean__axioms.Col Q B M) /\ (euclidean__axioms.Col B M Q)))) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.Col B Q M) /\ ((euclidean__axioms.Col Q B M) /\ (euclidean__axioms.Col B M Q))) as H44.
------------------------------------- exact H43.
------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col Q B M) /\ (euclidean__axioms.Col B M Q)) as H46.
-------------------------------------- exact H45.
-------------------------------------- destruct H46 as [H46 H47].
exact H46.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq Q B) as H40.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq Q M) /\ (euclidean__axioms.neq Q B))) as H40.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (Q) (M) (B) H22).
----------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M B) /\ ((euclidean__axioms.neq Q M) /\ (euclidean__axioms.neq Q B))) as H41.
------------------------------------ exact H40.
------------------------------------ destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.neq Q M) /\ (euclidean__axioms.neq Q B)) as H43.
------------------------------------- exact H42.
------------------------------------- destruct H43 as [H43 H44].
exact H44.
---------------------------------- assert (* Cut *) (euclidean__axioms.Col B F M) as H41.
----------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (F) (M)).
------------------------------------intro H41.
apply (@euclidean__tactics.Col__nCol__False (B) (F) (M) (H41)).
-------------------------------------apply (@lemma__collinear4.lemma__collinear4 (Q) (B) (F) (M) (H37) (H39) H40).


----------------------------------- assert (* Cut *) (euclidean__axioms.Col F M R) as H42.
------------------------------------ right.
right.
right.
right.
left.
exact H21.
------------------------------------ assert (* Cut *) (euclidean__axioms.Col M F B) as H43.
------------------------------------- assert (* Cut *) ((euclidean__axioms.Col F B M) /\ ((euclidean__axioms.Col F M B) /\ ((euclidean__axioms.Col M B F) /\ ((euclidean__axioms.Col B M F) /\ (euclidean__axioms.Col M F B))))) as H43.
-------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (F) (M) H41).
-------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col F B M) /\ ((euclidean__axioms.Col F M B) /\ ((euclidean__axioms.Col M B F) /\ ((euclidean__axioms.Col B M F) /\ (euclidean__axioms.Col M F B))))) as H44.
--------------------------------------- exact H43.
--------------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.Col F M B) /\ ((euclidean__axioms.Col M B F) /\ ((euclidean__axioms.Col B M F) /\ (euclidean__axioms.Col M F B)))) as H46.
---------------------------------------- exact H45.
---------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.Col M B F) /\ ((euclidean__axioms.Col B M F) /\ (euclidean__axioms.Col M F B))) as H48.
----------------------------------------- exact H47.
----------------------------------------- destruct H48 as [H48 H49].
assert (* AndElim *) ((euclidean__axioms.Col B M F) /\ (euclidean__axioms.Col M F B)) as H50.
------------------------------------------ exact H49.
------------------------------------------ destruct H50 as [H50 H51].
exact H51.
------------------------------------- assert (* Cut *) (euclidean__axioms.Col M F R) as H44.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M F R) /\ ((euclidean__axioms.Col M R F) /\ ((euclidean__axioms.Col R F M) /\ ((euclidean__axioms.Col F R M) /\ (euclidean__axioms.Col R M F))))) as H44.
--------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (M) (R) H42).
--------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col M F R) /\ ((euclidean__axioms.Col M R F) /\ ((euclidean__axioms.Col R F M) /\ ((euclidean__axioms.Col F R M) /\ (euclidean__axioms.Col R M F))))) as H45.
---------------------------------------- exact H44.
---------------------------------------- destruct H45 as [H45 H46].
assert (* AndElim *) ((euclidean__axioms.Col M R F) /\ ((euclidean__axioms.Col R F M) /\ ((euclidean__axioms.Col F R M) /\ (euclidean__axioms.Col R M F)))) as H47.
----------------------------------------- exact H46.
----------------------------------------- destruct H47 as [H47 H48].
assert (* AndElim *) ((euclidean__axioms.Col R F M) /\ ((euclidean__axioms.Col F R M) /\ (euclidean__axioms.Col R M F))) as H49.
------------------------------------------ exact H48.
------------------------------------------ destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col F R M) /\ (euclidean__axioms.Col R M F)) as H51.
------------------------------------------- exact H50.
------------------------------------------- destruct H51 as [H51 H52].
exact H45.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq F M) as H45.
--------------------------------------- assert (* Cut *) ((euclidean__axioms.neq M R) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F R))) as H45.
---------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (F) (M) (R) H21).
---------------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M R) /\ ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F R))) as H46.
----------------------------------------- exact H45.
----------------------------------------- destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.neq F M) /\ (euclidean__axioms.neq F R)) as H48.
------------------------------------------ exact H47.
------------------------------------------ destruct H48 as [H48 H49].
exact H48.
--------------------------------------- assert (* Cut *) (euclidean__axioms.neq M F) as H46.
---------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (F) (M) H45).
---------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B R) as H47.
----------------------------------------- apply (@euclidean__tactics.not__nCol__Col (F) (B) (R)).
------------------------------------------intro H47.
apply (@euclidean__tactics.Col__nCol__False (F) (B) (R) (H47)).
-------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (M) (F) (B) (R) (H43) (H44) H46).


----------------------------------------- assert (* Cut *) (euclidean__axioms.Col R B F) as H48.
------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col B F R) /\ ((euclidean__axioms.Col B R F) /\ ((euclidean__axioms.Col R F B) /\ ((euclidean__axioms.Col F R B) /\ (euclidean__axioms.Col R B F))))) as H48.
------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (F) (B) (R) H47).
------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col B F R) /\ ((euclidean__axioms.Col B R F) /\ ((euclidean__axioms.Col R F B) /\ ((euclidean__axioms.Col F R B) /\ (euclidean__axioms.Col R B F))))) as H49.
-------------------------------------------- exact H48.
-------------------------------------------- destruct H49 as [H49 H50].
assert (* AndElim *) ((euclidean__axioms.Col B R F) /\ ((euclidean__axioms.Col R F B) /\ ((euclidean__axioms.Col F R B) /\ (euclidean__axioms.Col R B F)))) as H51.
--------------------------------------------- exact H50.
--------------------------------------------- destruct H51 as [H51 H52].
assert (* AndElim *) ((euclidean__axioms.Col R F B) /\ ((euclidean__axioms.Col F R B) /\ (euclidean__axioms.Col R B F))) as H53.
---------------------------------------------- exact H52.
---------------------------------------------- destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col F R B) /\ (euclidean__axioms.Col R B F)) as H55.
----------------------------------------------- exact H54.
----------------------------------------------- destruct H55 as [H55 H56].
exact H56.
------------------------------------------ apply (@H18).
-------------------------------------------apply (@euclidean__tactics.not__nCol__Col (F) (P) (Q)).
--------------------------------------------intro H49.
apply (@euclidean__tactics.Col__nCol__False (R) (B) (F) (H35) H48).


------------------------------ assert (* Cut *) (euclidean__defs.CongA F B Q F B Q) as H37.
------------------------------- apply (@lemma__equalanglesreflexive.lemma__equalanglesreflexive (F) (B) (Q)).
--------------------------------apply (@euclidean__tactics.nCol__notCol (F) (B) (Q) H36).

------------------------------- assert (* Cut *) (euclidean__axioms.BetS B M Q) as H38.
-------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (Q) (M) (B) H22).
-------------------------------- assert (* Cut *) (euclidean__axioms.neq B M) as H39.
--------------------------------- assert (* Cut *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B Q))) as H39.
---------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal (B) (M) (Q) H38).
---------------------------------- assert (* AndElim *) ((euclidean__axioms.neq M Q) /\ ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B Q))) as H40.
----------------------------------- exact H39.
----------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.neq B M) /\ (euclidean__axioms.neq B Q)) as H42.
------------------------------------ exact H41.
------------------------------------ destruct H42 as [H42 H43].
exact H42.
--------------------------------- assert (* Cut *) (euclidean__defs.Out B M Q) as H40.
---------------------------------- apply (@lemma__ray4.lemma__ray4 (B) (M) (Q)).
-----------------------------------right.
right.
exact H38.

----------------------------------- exact H39.
---------------------------------- assert (* Cut *) (euclidean__defs.Out B Q M) as H41.
----------------------------------- apply (@lemma__ray5.lemma__ray5 (B) (M) (Q) H40).
----------------------------------- assert (* Cut *) (euclidean__defs.CongA F B Q F B M) as H42.
------------------------------------ apply (@lemma__equalangleshelper.lemma__equalangleshelper (F) (B) (Q) (F) (B) (Q) (F) (M) (H37) (H33) H41).
------------------------------------ assert (* Cut *) (euclidean__axioms.BetS R M F) as H43.
------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (F) (M) (R) H21).
------------------------------------- assert (* Cut *) (euclidean__defs.LtA F B Q F B R) as H44.
-------------------------------------- exists F.
exists M.
exists R.
split.
--------------------------------------- exact H21.
--------------------------------------- split.
---------------------------------------- exact H33.
---------------------------------------- split.
----------------------------------------- exact H27.
----------------------------------------- exact H42.
-------------------------------------- assert (* Cut *) (euclidean__defs.CongA f b d F B R) as H45.
--------------------------------------- apply (@lemma__equalanglesflip.lemma__equalanglesflip (d) (b) (f) (R) (B) (F) H34).
--------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B R f b d) as H46.
---------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (f) (b) (d) (F) (B) (R) H45).
---------------------------------------- assert (* Cut *) (euclidean__defs.LtA F B Q f b d) as H47.
----------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (F) (B) (Q) (F) (B) (R) (f) (b) (d) (H44) H45).
----------------------------------------- assert (* Cut *) (euclidean__defs.Out B Q D) as H48.
------------------------------------------ apply (@lemma__ray3.lemma__ray3 (B) (M) (Q) (D) (H40)).
-------------------------------------------apply (@lemma__ray3.lemma__ray3 (B) (Q) (M) (D) (H41)).
--------------------------------------------apply (@lemma__ray3.lemma__ray3 (B) (C) (Q) (D) (H10) H23).


------------------------------------------ assert (* Cut *) (euclidean__defs.CongA F B Q F B D) as H49.
------------------------------------------- apply (@lemma__equalangleshelper.lemma__equalangleshelper (F) (B) (Q) (F) (B) (Q) (F) (D) (H37) (H33) H48).
------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col F B D)) as H50.
-------------------------------------------- intro H50.
assert (* Cut *) (euclidean__axioms.Col B Q D) as H51.
--------------------------------------------- apply (@lemma__rayimpliescollinear.lemma__rayimpliescollinear (B) (Q) (D) H48).
--------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B Q) as H52.
---------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q B D) /\ ((euclidean__axioms.Col Q D B) /\ ((euclidean__axioms.Col D B Q) /\ ((euclidean__axioms.Col B D Q) /\ (euclidean__axioms.Col D Q B))))) as H52.
----------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (Q) (D) H51).
----------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q B D) /\ ((euclidean__axioms.Col Q D B) /\ ((euclidean__axioms.Col D B Q) /\ ((euclidean__axioms.Col B D Q) /\ (euclidean__axioms.Col D Q B))))) as H53.
------------------------------------------------ exact H52.
------------------------------------------------ destruct H53 as [H53 H54].
assert (* AndElim *) ((euclidean__axioms.Col Q D B) /\ ((euclidean__axioms.Col D B Q) /\ ((euclidean__axioms.Col B D Q) /\ (euclidean__axioms.Col D Q B)))) as H55.
------------------------------------------------- exact H54.
------------------------------------------------- destruct H55 as [H55 H56].
assert (* AndElim *) ((euclidean__axioms.Col D B Q) /\ ((euclidean__axioms.Col B D Q) /\ (euclidean__axioms.Col D Q B))) as H57.
-------------------------------------------------- exact H56.
-------------------------------------------------- destruct H57 as [H57 H58].
assert (* AndElim *) ((euclidean__axioms.Col B D Q) /\ (euclidean__axioms.Col D Q B)) as H59.
--------------------------------------------------- exact H58.
--------------------------------------------------- destruct H59 as [H59 H60].
exact H57.
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col D B F) as H53.
----------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col B F D) /\ ((euclidean__axioms.Col B D F) /\ ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F D B) /\ (euclidean__axioms.Col D B F))))) as H53.
------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder (F) (B) (D) H50).
------------------------------------------------ assert (* AndElim *) ((euclidean__axioms.Col B F D) /\ ((euclidean__axioms.Col B D F) /\ ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F D B) /\ (euclidean__axioms.Col D B F))))) as H54.
------------------------------------------------- exact H53.
------------------------------------------------- destruct H54 as [H54 H55].
assert (* AndElim *) ((euclidean__axioms.Col B D F) /\ ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F D B) /\ (euclidean__axioms.Col D B F)))) as H56.
-------------------------------------------------- exact H55.
-------------------------------------------------- destruct H56 as [H56 H57].
assert (* AndElim *) ((euclidean__axioms.Col D F B) /\ ((euclidean__axioms.Col F D B) /\ (euclidean__axioms.Col D B F))) as H58.
--------------------------------------------------- exact H57.
--------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col F D B) /\ (euclidean__axioms.Col D B F)) as H60.
---------------------------------------------------- exact H59.
---------------------------------------------------- destruct H60 as [H60 H61].
exact H61.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B D) as H54.
------------------------------------------------ apply (@lemma__raystrict.lemma__raystrict (B) (Q) (D) H48).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D B) as H55.
------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric (B) (D) H54).
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B Q F) as H56.
-------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col (B) (Q) (F)).
---------------------------------------------------intro H56.
apply (@euclidean__tactics.Col__nCol__False (B) (Q) (F) (H56)).
----------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 (D) (B) (Q) (F) (H52) (H53) H55).


-------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F B Q) as H57.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col Q B F) /\ ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F B Q) /\ ((euclidean__axioms.Col B F Q) /\ (euclidean__axioms.Col F Q B))))) as H57.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (B) (Q) (F) H56).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col Q B F) /\ ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F B Q) /\ ((euclidean__axioms.Col B F Q) /\ (euclidean__axioms.Col F Q B))))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col Q F B) /\ ((euclidean__axioms.Col F B Q) /\ ((euclidean__axioms.Col B F Q) /\ (euclidean__axioms.Col F Q B)))) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col F B Q) /\ ((euclidean__axioms.Col B F Q) /\ (euclidean__axioms.Col F Q B))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col B F Q) /\ (euclidean__axioms.Col F Q B)) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
exact H62.
--------------------------------------------------- apply (@H18).
----------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (F) (P) (Q)).
-----------------------------------------------------intro H58.
apply (@H36 H57).


-------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B D D B F) as H51.
--------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (F) (B) (D)).
----------------------------------------------apply (@euclidean__tactics.nCol__notCol (F) (B) (D) H50).

--------------------------------------------- assert (* Cut *) (euclidean__defs.CongA F B Q D B F) as H52.
---------------------------------------------- apply (@lemma__equalanglestransitive.lemma__equalanglestransitive (F) (B) (Q) (F) (B) (D) (D) (B) (F) (H49) H51).
---------------------------------------------- assert (* Cut *) (euclidean__defs.CongA D B F F B Q) as H53.
----------------------------------------------- apply (@lemma__equalanglessymmetric.lemma__equalanglessymmetric (F) (B) (Q) (D) (B) (F) H52).
----------------------------------------------- assert (* Cut *) (euclidean__defs.LtA D B F f b d) as H54.
------------------------------------------------ apply (@lemma__angleorderrespectscongruence2.lemma__angleorderrespectscongruence2 (F) (B) (Q) (f) (b) (d) (D) (B) (F) (H47) H53).
------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol f b d) as H55.
------------------------------------------------- apply (@euclidean__tactics.nCol__notCol (f) (b) (d)).
--------------------------------------------------apply (@euclidean__tactics.nCol__not__Col (f) (b) (d)).
---------------------------------------------------apply (@lemma__equalanglesNC.lemma__equalanglesNC (F) (B) (R) (f) (b) (d) H46).


------------------------------------------------- assert (* Cut *) (~(euclidean__axioms.Col d b f)) as H56.
-------------------------------------------------- intro H56.
assert (* Cut *) (euclidean__axioms.Col f b d) as H57.
--------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col b d f) /\ ((euclidean__axioms.Col b f d) /\ ((euclidean__axioms.Col f d b) /\ ((euclidean__axioms.Col d f b) /\ (euclidean__axioms.Col f b d))))) as H57.
---------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder (d) (b) (f) H56).
---------------------------------------------------- assert (* AndElim *) ((euclidean__axioms.Col b d f) /\ ((euclidean__axioms.Col b f d) /\ ((euclidean__axioms.Col f d b) /\ ((euclidean__axioms.Col d f b) /\ (euclidean__axioms.Col f b d))))) as H58.
----------------------------------------------------- exact H57.
----------------------------------------------------- destruct H58 as [H58 H59].
assert (* AndElim *) ((euclidean__axioms.Col b f d) /\ ((euclidean__axioms.Col f d b) /\ ((euclidean__axioms.Col d f b) /\ (euclidean__axioms.Col f b d)))) as H60.
------------------------------------------------------ exact H59.
------------------------------------------------------ destruct H60 as [H60 H61].
assert (* AndElim *) ((euclidean__axioms.Col f d b) /\ ((euclidean__axioms.Col d f b) /\ (euclidean__axioms.Col f b d))) as H62.
------------------------------------------------------- exact H61.
------------------------------------------------------- destruct H62 as [H62 H63].
assert (* AndElim *) ((euclidean__axioms.Col d f b) /\ (euclidean__axioms.Col f b d)) as H64.
-------------------------------------------------------- exact H63.
-------------------------------------------------------- destruct H64 as [H64 H65].
exact H65.
--------------------------------------------------- apply (@H18).
----------------------------------------------------apply (@euclidean__tactics.not__nCol__Col (F) (P) (Q)).
-----------------------------------------------------intro H58.
apply (@euclidean__tactics.Col__nCol__False (f) (b) (d) (H55) H57).


-------------------------------------------------- assert (* Cut *) (euclidean__defs.CongA d b f f b d) as H57.
--------------------------------------------------- apply (@lemma__ABCequalsCBA.lemma__ABCequalsCBA (d) (b) (f)).
----------------------------------------------------apply (@euclidean__tactics.nCol__notCol (d) (b) (f) H56).

--------------------------------------------------- assert (* Cut *) (euclidean__defs.LtA D B F d b f) as H58.
---------------------------------------------------- apply (@lemma__angleorderrespectscongruence.lemma__angleorderrespectscongruence (D) (B) (F) (f) (b) (d) (d) (b) (f) (H54) H57).
---------------------------------------------------- exact H58.
Qed.
