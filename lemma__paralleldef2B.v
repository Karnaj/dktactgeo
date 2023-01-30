Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__7b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinear5.
Require Export lemma__collinearorder.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__parallelcollinear.
Require Export lemma__tarskiparallelflip.
Require Export logic.
Definition lemma__paralleldef2B : forall A B C D, (euclidean__defs.Par A B C D) -> (euclidean__defs.TP A B C D).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (exists a b c d e, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.neq a b) /\ ((euclidean__axioms.Col C D c) /\ ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.neq c d) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS a e d) /\ (euclidean__axioms.BetS c e b))))))))))) as H0 by exact H.
destruct H0 as [a H1].
destruct H1 as [b H2].
destruct H2 as [c H3].
destruct H3 as [d H4].
destruct H4 as [e H5].
destruct H5 as [H6 H7].
destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
assert (* Cut *) (euclidean__axioms.neq b a) as H26.
- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric a b H14).
- assert (* Cut *) (euclidean__axioms.neq e b) as H27.
-- assert (* Cut *) ((euclidean__axioms.neq e b) /\ ((euclidean__axioms.neq c e) /\ (euclidean__axioms.neq c b))) as H27.
--- apply (@lemma__betweennotequal.lemma__betweennotequal c e b H25).
--- destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
exact H28.
-- assert (* Cut *) (~(euclidean__defs.Meet a b C D)) as H28.
--- intro H28.
assert (exists R, (euclidean__axioms.neq a b) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col a b R) /\ (euclidean__axioms.Col C D R)))) as H29 by exact H28.
destruct H29 as [R H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
assert (* Cut *) (euclidean__axioms.Col b a R) as H37.
---- assert (* Cut *) ((euclidean__axioms.Col b a R) /\ ((euclidean__axioms.Col b R a) /\ ((euclidean__axioms.Col R a b) /\ ((euclidean__axioms.Col a R b) /\ (euclidean__axioms.Col R b a))))) as H37.
----- apply (@lemma__collinearorder.lemma__collinearorder a b R H35).
----- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H38.
---- assert (* Cut *) (euclidean__axioms.Col B a b) as H38.
----- apply (@euclidean__tactics.not__nCol__Col B a b).
------intro H38.
apply (@euclidean__tactics.Col__nCol__False B a b H38).
-------apply (@lemma__collinear4.lemma__collinear4 A B a b H10 H12 H6).


----- assert (* Cut *) (euclidean__axioms.Col b a B) as H39.
------ assert (* Cut *) ((euclidean__axioms.Col a B b) /\ ((euclidean__axioms.Col a b B) /\ ((euclidean__axioms.Col b B a) /\ ((euclidean__axioms.Col B b a) /\ (euclidean__axioms.Col b a B))))) as H39.
------- apply (@lemma__collinearorder.lemma__collinearorder B a b H38).
------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H47.
------ assert (* Cut *) (euclidean__axioms.Col a B R) as H40.
------- apply (@euclidean__tactics.not__nCol__Col a B R).
--------intro H40.
apply (@euclidean__tactics.Col__nCol__False a B R H40).
---------apply (@lemma__collinear4.lemma__collinear4 b a B R H39 H37 H26).


------- assert (* Cut *) (euclidean__axioms.Col a B A) as H41.
-------- assert (* Cut *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H41.
--------- apply (@lemma__collinearorder.lemma__collinearorder A B a H10).
--------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
-------- assert (* Cut *) (euclidean__axioms.Col A B R) as H42.
--------- assert (* Cut *) ((euclidean__axioms.neq a B) \/ (a = B)) as H42.
---------- apply (@euclidean__tactics.neq__or__eq a B).
---------- assert ((euclidean__axioms.neq a B) \/ (a = B)) as H43 by exact H42.
assert ((euclidean__axioms.neq a B) \/ (a = B)) as __TmpHyp by exact H43.
destruct __TmpHyp as [H44|H44].
----------- assert (* Cut *) (euclidean__axioms.Col B R A) as H45.
------------ apply (@euclidean__tactics.not__nCol__Col B R A).
-------------intro H45.
apply (@euclidean__tactics.Col__nCol__False B R A H45).
--------------apply (@lemma__collinear4.lemma__collinear4 a B R A H40 H41 H44).


------------ assert (* Cut *) (euclidean__axioms.Col A B R) as H46.
------------- assert (* Cut *) ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col A B R) /\ ((euclidean__axioms.Col B A R) /\ (euclidean__axioms.Col A R B))))) as H46.
-------------- apply (@lemma__collinearorder.lemma__collinearorder B R A H45).
-------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H51.
------------- exact H46.
----------- assert (* Cut *) (euclidean__axioms.neq A a) as H45.
------------ apply (@eq__ind__r euclidean__axioms.Point B (fun a0 => (euclidean__axioms.Col A B a0) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.BetS a0 e d) -> ((euclidean__axioms.neq b a0) -> ((euclidean__defs.Meet a0 b C D) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.Col a0 b R) -> ((euclidean__axioms.Col b a0 R) -> ((euclidean__axioms.Col B a0 b) -> ((euclidean__axioms.Col b a0 B) -> ((euclidean__axioms.Col a0 B R) -> ((euclidean__axioms.Col a0 B A) -> (euclidean__axioms.neq A a0)))))))))))))) with (x := a).
-------------intro H45.
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
exact H6.

------------- exact H44.
------------- exact H10.
------------- exact H14.
------------- exact H24.
------------- exact H26.
------------- exact H28.
------------- exact H31.
------------- exact H35.
------------- exact H37.
------------- exact H38.
------------- exact H39.
------------- exact H40.
------------- exact H41.
------------ assert (* Cut *) (euclidean__axioms.Col B A a) as H46.
------------- assert (* Cut *) ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col A a B) /\ ((euclidean__axioms.Col a A B) /\ (euclidean__axioms.Col A B a))))) as H46.
-------------- apply (@lemma__collinearorder.lemma__collinearorder a B A H41).
-------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H49.
------------- assert (* Cut *) (euclidean__axioms.Col B A b) as H47.
-------------- assert (* Cut *) ((euclidean__axioms.Col B A b) /\ ((euclidean__axioms.Col B b A) /\ ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col A b B) /\ (euclidean__axioms.Col b B A))))) as H47.
--------------- apply (@lemma__collinearorder.lemma__collinearorder A B b H12).
--------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H48.
-------------- assert (* Cut *) (euclidean__axioms.neq B A) as H48.
--------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A B H6).
--------------- assert (* Cut *) (euclidean__axioms.Col A a b) as H49.
---------------- apply (@eq__ind__r euclidean__axioms.Point B (fun a0 => (euclidean__axioms.Col A B a0) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.BetS a0 e d) -> ((euclidean__axioms.neq b a0) -> ((euclidean__defs.Meet a0 b C D) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.Col a0 b R) -> ((euclidean__axioms.Col b a0 R) -> ((euclidean__axioms.Col B a0 b) -> ((euclidean__axioms.Col b a0 B) -> ((euclidean__axioms.Col a0 B R) -> ((euclidean__axioms.Col a0 B A) -> ((euclidean__axioms.neq A a0) -> ((euclidean__axioms.Col B A a0) -> (euclidean__axioms.Col A a0 b)))))))))))))))) with (x := a).
-----------------intro H49.
intro H50.
intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
exact H12.

----------------- exact H44.
----------------- exact H10.
----------------- exact H14.
----------------- exact H24.
----------------- exact H26.
----------------- exact H28.
----------------- exact H31.
----------------- exact H35.
----------------- exact H37.
----------------- exact H38.
----------------- exact H39.
----------------- exact H40.
----------------- exact H41.
----------------- exact H45.
----------------- exact H46.
---------------- assert (* Cut *) (euclidean__axioms.Col b a A) as H50.
----------------- assert (* Cut *) ((euclidean__axioms.Col a A b) /\ ((euclidean__axioms.Col a b A) /\ ((euclidean__axioms.Col b A a) /\ ((euclidean__axioms.Col A b a) /\ (euclidean__axioms.Col b a A))))) as H50.
------------------ apply (@lemma__collinearorder.lemma__collinearorder A a b H49).
------------------ destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H58.
----------------- assert (* Cut *) (euclidean__axioms.Col a A R) as H51.
------------------ apply (@euclidean__tactics.not__nCol__Col a A R).
-------------------intro H51.
apply (@euclidean__tactics.Col__nCol__False a A R H51).
--------------------apply (@lemma__collinear4.lemma__collinear4 b a A R H50 H37 H26).


------------------ assert (* Cut *) (euclidean__axioms.Col a A B) as H52.
------------------- assert (* Cut *) ((euclidean__axioms.Col A B a) /\ ((euclidean__axioms.Col A a B) /\ ((euclidean__axioms.Col a B A) /\ ((euclidean__axioms.Col B a A) /\ (euclidean__axioms.Col a A B))))) as H52.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder B A a H46).
-------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H60.
------------------- assert (* Cut *) (euclidean__axioms.neq A a) as H53.
-------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun a0 => (euclidean__axioms.Col A B a0) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.BetS a0 e d) -> ((euclidean__axioms.neq b a0) -> ((euclidean__defs.Meet a0 b C D) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.Col a0 b R) -> ((euclidean__axioms.Col b a0 R) -> ((euclidean__axioms.Col B a0 b) -> ((euclidean__axioms.Col b a0 B) -> ((euclidean__axioms.Col a0 B R) -> ((euclidean__axioms.Col a0 B A) -> ((euclidean__axioms.neq A a0) -> ((euclidean__axioms.Col B A a0) -> ((euclidean__axioms.Col A a0 b) -> ((euclidean__axioms.Col b a0 A) -> ((euclidean__axioms.Col a0 A R) -> ((euclidean__axioms.Col a0 A B) -> (euclidean__axioms.neq A a0)))))))))))))))))))) with (x := a).
---------------------intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
exact H65.

--------------------- exact H44.
--------------------- exact H10.
--------------------- exact H14.
--------------------- exact H24.
--------------------- exact H26.
--------------------- exact H28.
--------------------- exact H31.
--------------------- exact H35.
--------------------- exact H37.
--------------------- exact H38.
--------------------- exact H39.
--------------------- exact H40.
--------------------- exact H41.
--------------------- exact H45.
--------------------- exact H46.
--------------------- exact H49.
--------------------- exact H50.
--------------------- exact H51.
--------------------- exact H52.
-------------------- assert (* Cut *) (euclidean__axioms.neq a A) as H54.
--------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun a0 => (euclidean__axioms.Col A B a0) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.BetS a0 e d) -> ((euclidean__axioms.neq b a0) -> ((euclidean__defs.Meet a0 b C D) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.Col a0 b R) -> ((euclidean__axioms.Col b a0 R) -> ((euclidean__axioms.Col B a0 b) -> ((euclidean__axioms.Col b a0 B) -> ((euclidean__axioms.Col a0 B R) -> ((euclidean__axioms.Col a0 B A) -> ((euclidean__axioms.neq A a0) -> ((euclidean__axioms.Col B A a0) -> ((euclidean__axioms.Col A a0 b) -> ((euclidean__axioms.Col b a0 A) -> ((euclidean__axioms.Col a0 A R) -> ((euclidean__axioms.Col a0 A B) -> ((euclidean__axioms.neq A a0) -> (euclidean__axioms.neq a0 A))))))))))))))))))))) with (x := a).
----------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
intro H71.
intro H72.
exact H48.

---------------------- exact H44.
---------------------- exact H10.
---------------------- exact H14.
---------------------- exact H24.
---------------------- exact H26.
---------------------- exact H28.
---------------------- exact H31.
---------------------- exact H35.
---------------------- exact H37.
---------------------- exact H38.
---------------------- exact H39.
---------------------- exact H40.
---------------------- exact H41.
---------------------- exact H45.
---------------------- exact H46.
---------------------- exact H49.
---------------------- exact H50.
---------------------- exact H51.
---------------------- exact H52.
---------------------- exact H53.
--------------------- assert (* Cut *) (euclidean__axioms.Col A R B) as H55.
---------------------- apply (@euclidean__tactics.not__nCol__Col A R B).
-----------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False A R B H55).
------------------------apply (@lemma__collinear4.lemma__collinear4 a A R B H51 H52 H54).


---------------------- assert (* Cut *) (euclidean__axioms.Col A B R) as H56.
----------------------- assert (* Cut *) ((euclidean__axioms.Col R A B) /\ ((euclidean__axioms.Col R B A) /\ ((euclidean__axioms.Col B A R) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.Col B R A))))) as H56.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder A R B H55).
------------------------ destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H63.
----------------------- exact H56.
--------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H43.
---------- exists R.
split.
----------- exact H6.
----------- split.
------------ exact H33.
------------ split.
------------- exact H42.
------------- exact H36.
---------- apply (@H22 H43).
--- assert (* Cut *) (exists P, (euclidean__axioms.BetS e b P) /\ (euclidean__axioms.Cong b P e b)) as H29.
---- apply (@lemma__extension.lemma__extension e b e b H27 H27).
---- destruct H29 as [P H30].
destruct H30 as [H31 H32].
assert (* Cut *) (euclidean__axioms.BetS P b e) as H33.
----- apply (@euclidean__axioms.axiom__betweennesssymmetry e b P H31).
----- assert (* Cut *) (euclidean__axioms.BetS b e c) as H34.
------ apply (@euclidean__axioms.axiom__betweennesssymmetry c e b H25).
------ assert (* Cut *) (euclidean__axioms.BetS P b c) as H35.
------- apply (@lemma__3__7b.lemma__3__7b P b e c H33 H34).
------- assert (* Cut *) (euclidean__axioms.BetS c b P) as H36.
-------- apply (@euclidean__axioms.axiom__betweennesssymmetry P b c H35).
-------- assert (* Cut *) (~(euclidean__axioms.Col a d P)) as H37.
--------- intro H37.
assert (* Cut *) (euclidean__axioms.Col a e d) as H38.
---------- right.
right.
right.
right.
left.
exact H24.
---------- assert (* Cut *) (euclidean__axioms.Col a d e) as H39.
----------- assert (* Cut *) ((euclidean__axioms.Col e a d) /\ ((euclidean__axioms.Col e d a) /\ ((euclidean__axioms.Col d a e) /\ ((euclidean__axioms.Col a d e) /\ (euclidean__axioms.Col d e a))))) as H39.
------------ apply (@lemma__collinearorder.lemma__collinearorder a e d H38).
------------ destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
exact H46.
----------- assert (* Cut *) (euclidean__axioms.neq a d) as H40.
------------ assert (* Cut *) ((euclidean__axioms.neq e d) /\ ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a d))) as H40.
------------- apply (@lemma__betweennotequal.lemma__betweennotequal a e d H24).
------------- destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H44.
------------ assert (* Cut *) (euclidean__axioms.Col d P e) as H41.
------------- apply (@euclidean__tactics.not__nCol__Col d P e).
--------------intro H41.
apply (@euclidean__tactics.Col__nCol__False d P e H41).
---------------apply (@lemma__collinear4.lemma__collinear4 a d P e H37 H39 H40).


------------- assert (* Cut *) (euclidean__axioms.Col e P d) as H42.
-------------- assert (* Cut *) ((euclidean__axioms.Col P d e) /\ ((euclidean__axioms.Col P e d) /\ ((euclidean__axioms.Col e d P) /\ ((euclidean__axioms.Col d e P) /\ (euclidean__axioms.Col e P d))))) as H42.
--------------- apply (@lemma__collinearorder.lemma__collinearorder d P e H41).
--------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H50.
-------------- assert (* Cut *) (euclidean__axioms.Col e b P) as H43.
--------------- right.
right.
right.
right.
left.
exact H31.
--------------- assert (* Cut *) (euclidean__axioms.Col e P b) as H44.
---------------- assert (* Cut *) ((euclidean__axioms.Col b e P) /\ ((euclidean__axioms.Col b P e) /\ ((euclidean__axioms.Col P e b) /\ ((euclidean__axioms.Col e P b) /\ (euclidean__axioms.Col P b e))))) as H44.
----------------- apply (@lemma__collinearorder.lemma__collinearorder e b P H43).
----------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
exact H51.
---------------- assert (* Cut *) (euclidean__axioms.neq e P) as H45.
----------------- assert (* Cut *) ((euclidean__axioms.neq b P) /\ ((euclidean__axioms.neq e b) /\ (euclidean__axioms.neq e P))) as H45.
------------------ apply (@lemma__betweennotequal.lemma__betweennotequal e b P H31).
------------------ destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H49.
----------------- assert (* Cut *) (euclidean__axioms.Col P d b) as H46.
------------------ apply (@euclidean__tactics.not__nCol__Col P d b).
-------------------intro H46.
apply (@euclidean__tactics.Col__nCol__False P d b H46).
--------------------apply (@lemma__collinear4.lemma__collinear4 e P d b H42 H44 H45).


------------------ assert (* Cut *) (euclidean__axioms.Col d P b) as H47.
------------------- assert (* Cut *) ((euclidean__axioms.Col d P b) /\ ((euclidean__axioms.Col d b P) /\ ((euclidean__axioms.Col b P d) /\ ((euclidean__axioms.Col P b d) /\ (euclidean__axioms.Col b d P))))) as H47.
-------------------- apply (@lemma__collinearorder.lemma__collinearorder P d b H46).
-------------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H48.
------------------- assert (* Cut *) (euclidean__axioms.Col d P a) as H48.
-------------------- assert (* Cut *) ((euclidean__axioms.Col d a P) /\ ((euclidean__axioms.Col d P a) /\ ((euclidean__axioms.Col P a d) /\ ((euclidean__axioms.Col a P d) /\ (euclidean__axioms.Col P d a))))) as H48.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder a d P H37).
--------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H51.
-------------------- assert (* Cut *) (~(d = P)) as H49.
--------------------- intro H49.
assert (* Cut *) (euclidean__axioms.Col c b P) as H50.
---------------------- right.
right.
right.
right.
left.
exact H36.
---------------------- assert (* Cut *) (euclidean__axioms.Col c b d) as H51.
----------------------- apply (@eq__ind__r euclidean__axioms.Point P (fun d0 => (euclidean__axioms.Col C D d0) -> ((euclidean__axioms.neq c d0) -> ((euclidean__axioms.BetS a e d0) -> ((euclidean__axioms.Col a d0 P) -> ((euclidean__axioms.Col a e d0) -> ((euclidean__axioms.Col a d0 e) -> ((euclidean__axioms.neq a d0) -> ((euclidean__axioms.Col d0 P e) -> ((euclidean__axioms.Col e P d0) -> ((euclidean__axioms.Col P d0 b) -> ((euclidean__axioms.Col d0 P b) -> ((euclidean__axioms.Col d0 P a) -> (euclidean__axioms.Col c b d0)))))))))))))) with (x := d).
------------------------intro H51.
intro H52.
intro H53.
intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
exact H50.

------------------------ exact H49.
------------------------ exact H18.
------------------------ exact H20.
------------------------ exact H24.
------------------------ exact H37.
------------------------ exact H38.
------------------------ exact H39.
------------------------ exact H40.
------------------------ exact H41.
------------------------ exact H42.
------------------------ exact H46.
------------------------ exact H47.
------------------------ exact H48.
----------------------- assert (* Cut *) (euclidean__axioms.Col b e c) as H52.
------------------------ right.
right.
right.
right.
left.
exact H34.
------------------------ assert (* Cut *) (euclidean__axioms.Col c b e) as H53.
------------------------- assert (* Cut *) ((euclidean__axioms.Col e b c) /\ ((euclidean__axioms.Col e c b) /\ ((euclidean__axioms.Col c b e) /\ ((euclidean__axioms.Col b c e) /\ (euclidean__axioms.Col c e b))))) as H53.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder b e c H52).
-------------------------- destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
exact H58.
------------------------- assert (* Cut *) (euclidean__axioms.neq c b) as H54.
-------------------------- assert (* Cut *) ((euclidean__axioms.neq b P) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c P))) as H54.
--------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal c b P H36).
--------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H57.
-------------------------- assert (* Cut *) (euclidean__axioms.Col b d e) as H55.
--------------------------- apply (@euclidean__tactics.not__nCol__Col b d e).
----------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False b d e H55).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 c b d e H51 H53 H54).


--------------------------- assert (euclidean__axioms.Col a e d) as H56 by exact H38.
assert (* Cut *) (euclidean__axioms.Col d e a) as H57.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col e a d) /\ ((euclidean__axioms.Col e d a) /\ ((euclidean__axioms.Col d a e) /\ ((euclidean__axioms.Col a d e) /\ (euclidean__axioms.Col d e a))))) as H57.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder a e d H56).
----------------------------- destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H65.
---------------------------- assert (* Cut *) (euclidean__axioms.Col d e b) as H58.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col d b e) /\ ((euclidean__axioms.Col d e b) /\ ((euclidean__axioms.Col e b d) /\ ((euclidean__axioms.Col b e d) /\ (euclidean__axioms.Col e d b))))) as H58.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder b d e H55).
------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H61.
----------------------------- assert (* Cut *) (euclidean__axioms.neq e d) as H59.
------------------------------ assert (* Cut *) ((euclidean__axioms.neq e d) /\ ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a d))) as H59.
------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal a e d H24).
------------------------------- destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
------------------------------ assert (* Cut *) (euclidean__axioms.neq d e) as H60.
------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric e d H59).
------------------------------- assert (* Cut *) (euclidean__axioms.Col e a b) as H61.
-------------------------------- apply (@euclidean__tactics.not__nCol__Col e a b).
---------------------------------intro H61.
apply (@euclidean__tactics.Col__nCol__False e a b H61).
----------------------------------apply (@lemma__collinear4.lemma__collinear4 d e a b H57 H58 H60).


-------------------------------- assert (euclidean__axioms.Col a e d) as H62 by exact H56.
assert (* Cut *) (euclidean__axioms.Col e a d) as H63.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col e a d) /\ ((euclidean__axioms.Col e d a) /\ ((euclidean__axioms.Col d a e) /\ ((euclidean__axioms.Col a d e) /\ (euclidean__axioms.Col d e a))))) as H63.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder a e d H62).
---------------------------------- destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
exact H64.
--------------------------------- assert (* Cut *) (euclidean__axioms.neq a e) as H64.
---------------------------------- assert (* Cut *) ((euclidean__axioms.neq e d) /\ ((euclidean__axioms.neq a e) /\ (euclidean__axioms.neq a d))) as H64.
----------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal a e d H24).
----------------------------------- destruct H64 as [H65 H66].
destruct H66 as [H67 H68].
exact H67.
---------------------------------- assert (* Cut *) (euclidean__axioms.neq e a) as H65.
----------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric a e H64).
----------------------------------- assert (* Cut *) (euclidean__axioms.Col a b d) as H66.
------------------------------------ apply (@euclidean__tactics.not__nCol__Col a b d).
-------------------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False a b d H66).
--------------------------------------apply (@lemma__collinear4.lemma__collinear4 e a b d H61 H63 H65).


------------------------------------ assert (* Cut *) (euclidean__defs.Meet a b C D) as H67.
------------------------------------- exists d.
split.
-------------------------------------- exact H14.
-------------------------------------- split.
--------------------------------------- exact H8.
--------------------------------------- split.
---------------------------------------- exact H66.
---------------------------------------- exact H18.
------------------------------------- apply (@H28 H67).
--------------------- assert (* Cut *) (euclidean__axioms.Col P b a) as H50.
---------------------- apply (@euclidean__tactics.not__nCol__Col P b a).
-----------------------intro H50.
apply (@euclidean__tactics.Col__nCol__False P b a H50).
------------------------apply (@lemma__collinear4.lemma__collinear4 d P b a H47 H48 H49).


---------------------- assert (* Cut *) (euclidean__axioms.Col P b c) as H51.
----------------------- right.
right.
right.
right.
left.
exact H35.
----------------------- assert (* Cut *) (euclidean__axioms.neq b P) as H52.
------------------------ assert (* Cut *) ((euclidean__axioms.neq b P) /\ ((euclidean__axioms.neq c b) /\ (euclidean__axioms.neq c P))) as H52.
------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal c b P H36).
------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
------------------------ assert (* Cut *) (euclidean__axioms.neq P b) as H53.
------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric b P H52).
------------------------- assert (* Cut *) (euclidean__axioms.Col b a c) as H54.
-------------------------- apply (@euclidean__tactics.not__nCol__Col b a c).
---------------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False b a c H54).
----------------------------apply (@lemma__collinear4.lemma__collinear4 P b a c H50 H51 H53).


-------------------------- assert (* Cut *) (euclidean__axioms.Col B a b) as H55.
--------------------------- apply (@euclidean__tactics.not__nCol__Col B a b).
----------------------------intro H55.
apply (@euclidean__tactics.Col__nCol__False B a b H55).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 A B a b H10 H12 H6).


--------------------------- assert (* Cut *) (euclidean__axioms.Col b a B) as H56.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col a B b) /\ ((euclidean__axioms.Col a b B) /\ ((euclidean__axioms.Col b B a) /\ ((euclidean__axioms.Col B b a) /\ (euclidean__axioms.Col b a B))))) as H56.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder B a b H55).
----------------------------- destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
---------------------------- assert (* Cut *) (euclidean__axioms.Col a b c) as H57.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col a b c) /\ ((euclidean__axioms.Col a c b) /\ ((euclidean__axioms.Col c b a) /\ ((euclidean__axioms.Col b c a) /\ (euclidean__axioms.Col c a b))))) as H57.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder b a c H54).
------------------------------ destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
exact H58.
----------------------------- assert (* Cut *) (c = c) as H58.
------------------------------ apply (@logic.eq__refl Point c).
------------------------------ assert (* Cut *) (euclidean__defs.Meet a b C D) as H59.
------------------------------- exists c.
split.
-------------------------------- exact H14.
-------------------------------- split.
--------------------------------- exact H8.
--------------------------------- split.
---------------------------------- exact H57.
---------------------------------- exact H16.
------------------------------- apply (@H28 H59).
--------- assert (* Cut *) (exists M, (euclidean__axioms.BetS P M d) /\ (euclidean__axioms.BetS a b M)) as H38.
---------- apply (@euclidean__axioms.postulate__Pasch__outer P a e b d H33 H24).
-----------apply (@euclidean__tactics.nCol__notCol a d P H37).

---------- destruct H38 as [M H39].
destruct H39 as [H40 H41].
assert (* Cut *) (euclidean__axioms.BetS M b a) as H42.
----------- apply (@euclidean__axioms.axiom__betweennesssymmetry a b M H41).
----------- assert (euclidean__axioms.BetS P b c) as H43 by exact H35.
assert (* Cut *) (euclidean__axioms.Col a b M) as H44.
------------ right.
right.
right.
right.
left.
exact H41.
------------ assert (* Cut *) (euclidean__axioms.Col B a b) as H45.
------------- apply (@euclidean__tactics.not__nCol__Col B a b).
--------------intro H45.
apply (@euclidean__tactics.Col__nCol__False B a b H45).
---------------apply (@lemma__collinear4.lemma__collinear4 A B a b H10 H12 H6).


------------- assert (* Cut *) (euclidean__axioms.Col b a B) as H46.
-------------- assert (* Cut *) ((euclidean__axioms.Col a B b) /\ ((euclidean__axioms.Col a b B) /\ ((euclidean__axioms.Col b B a) /\ ((euclidean__axioms.Col B b a) /\ (euclidean__axioms.Col b a B))))) as H46.
--------------- apply (@lemma__collinearorder.lemma__collinearorder B a b H45).
--------------- destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
exact H54.
-------------- assert (* Cut *) (euclidean__axioms.Col b a M) as H47.
--------------- assert (* Cut *) ((euclidean__axioms.Col b a M) /\ ((euclidean__axioms.Col b M a) /\ ((euclidean__axioms.Col M a b) /\ ((euclidean__axioms.Col a M b) /\ (euclidean__axioms.Col M b a))))) as H47.
---------------- apply (@lemma__collinearorder.lemma__collinearorder a b M H44).
---------------- destruct H47 as [H48 H49].
destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
exact H48.
--------------- assert (euclidean__axioms.neq b a) as H48 by exact H26.
assert (* Cut *) (euclidean__axioms.Col a B M) as H49.
---------------- apply (@euclidean__tactics.not__nCol__Col a B M).
-----------------intro H49.
apply (@euclidean__tactics.Col__nCol__False a B M H49).
------------------apply (@lemma__collinear4.lemma__collinear4 b a B M H46 H47 H48).


---------------- assert (* Cut *) (euclidean__axioms.Col a B A) as H50.
----------------- assert (* Cut *) ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col a A B) /\ ((euclidean__axioms.Col A a B) /\ (euclidean__axioms.Col a B A))))) as H50.
------------------ apply (@lemma__collinearorder.lemma__collinearorder A B a H10).
------------------ destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H58.
----------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H51.
------------------ assert (* Cut *) ((euclidean__axioms.neq a B) \/ (a = B)) as H51.
------------------- apply (@euclidean__tactics.neq__or__eq a B).
------------------- assert ((euclidean__axioms.neq a B) \/ (a = B)) as H52 by exact H51.
assert ((euclidean__axioms.neq a B) \/ (a = B)) as __TmpHyp by exact H52.
destruct __TmpHyp as [H53|H53].
-------------------- assert (* Cut *) (euclidean__axioms.Col B M A) as H54.
--------------------- apply (@euclidean__tactics.not__nCol__Col B M A).
----------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False B M A H54).
-----------------------apply (@lemma__collinear4.lemma__collinear4 a B M A H49 H50 H53).


--------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H55.
---------------------- assert (* Cut *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H55.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder B M A H54).
----------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
---------------------- exact H55.
-------------------- assert (* Cut *) (euclidean__axioms.neq A a) as H54.
--------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun a0 => (euclidean__axioms.Col A B a0) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.BetS a0 e d) -> ((euclidean__axioms.neq b a0) -> ((~(euclidean__defs.Meet a0 b C D)) -> ((~(euclidean__axioms.Col a0 d P)) -> ((euclidean__axioms.BetS a0 b M) -> ((euclidean__axioms.BetS M b a0) -> ((euclidean__axioms.Col a0 b M) -> ((euclidean__axioms.Col B a0 b) -> ((euclidean__axioms.Col b a0 B) -> ((euclidean__axioms.Col b a0 M) -> ((euclidean__axioms.neq b a0) -> ((euclidean__axioms.Col a0 B M) -> ((euclidean__axioms.Col a0 B A) -> (euclidean__axioms.neq A a0))))))))))))))))) with (x := a).
----------------------intro H54.
intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
exact H6.

---------------------- exact H53.
---------------------- exact H10.
---------------------- exact H14.
---------------------- exact H24.
---------------------- exact H26.
---------------------- exact H28.
---------------------- exact H37.
---------------------- exact H41.
---------------------- exact H42.
---------------------- exact H44.
---------------------- exact H45.
---------------------- exact H46.
---------------------- exact H47.
---------------------- exact H48.
---------------------- exact H49.
---------------------- exact H50.
--------------------- assert (* Cut *) (euclidean__axioms.Col A a b) as H55.
---------------------- apply (@eq__ind__r euclidean__axioms.Point B (fun a0 => (euclidean__axioms.Col A B a0) -> ((euclidean__axioms.neq a0 b) -> ((euclidean__axioms.BetS a0 e d) -> ((euclidean__axioms.neq b a0) -> ((~(euclidean__defs.Meet a0 b C D)) -> ((~(euclidean__axioms.Col a0 d P)) -> ((euclidean__axioms.BetS a0 b M) -> ((euclidean__axioms.BetS M b a0) -> ((euclidean__axioms.Col a0 b M) -> ((euclidean__axioms.Col B a0 b) -> ((euclidean__axioms.Col b a0 B) -> ((euclidean__axioms.Col b a0 M) -> ((euclidean__axioms.neq b a0) -> ((euclidean__axioms.Col a0 B M) -> ((euclidean__axioms.Col a0 B A) -> ((euclidean__axioms.neq A a0) -> (euclidean__axioms.Col A a0 b)))))))))))))))))) with (x := a).
-----------------------intro H55.
intro H56.
intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
intro H65.
intro H66.
intro H67.
intro H68.
intro H69.
intro H70.
exact H12.

----------------------- exact H53.
----------------------- exact H10.
----------------------- exact H14.
----------------------- exact H24.
----------------------- exact H26.
----------------------- exact H28.
----------------------- exact H37.
----------------------- exact H41.
----------------------- exact H42.
----------------------- exact H44.
----------------------- exact H45.
----------------------- exact H46.
----------------------- exact H47.
----------------------- exact H48.
----------------------- exact H49.
----------------------- exact H50.
----------------------- exact H54.
---------------------- assert (* Cut *) (euclidean__axioms.Col b a A) as H56.
----------------------- assert (* Cut *) ((euclidean__axioms.Col a A b) /\ ((euclidean__axioms.Col a b A) /\ ((euclidean__axioms.Col b A a) /\ ((euclidean__axioms.Col A b a) /\ (euclidean__axioms.Col b a A))))) as H56.
------------------------ apply (@lemma__collinearorder.lemma__collinearorder A a b H55).
------------------------ destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H64.
----------------------- assert (* Cut *) (euclidean__axioms.Col a A M) as H57.
------------------------ apply (@euclidean__tactics.not__nCol__Col a A M).
-------------------------intro H57.
apply (@euclidean__tactics.Col__nCol__False a A M H57).
--------------------------apply (@lemma__collinear4.lemma__collinear4 b a A M H56 H47 H48).


------------------------ assert (* Cut *) (euclidean__axioms.Col a A B) as H58.
------------------------- assert (* Cut *) ((euclidean__axioms.Col B a A) /\ ((euclidean__axioms.Col B A a) /\ ((euclidean__axioms.Col A a B) /\ ((euclidean__axioms.Col a A B) /\ (euclidean__axioms.Col A B a))))) as H58.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder a B A H50).
-------------------------- destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
------------------------- assert (* Cut *) (euclidean__axioms.neq a A) as H59.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A a H54).
-------------------------- assert (* Cut *) (euclidean__axioms.Col A M B) as H60.
--------------------------- apply (@euclidean__tactics.not__nCol__Col A M B).
----------------------------intro H60.
apply (@euclidean__tactics.Col__nCol__False A M B H60).
-----------------------------apply (@lemma__collinear4.lemma__collinear4 a A M B H57 H58 H59).


--------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H61.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col B A M) /\ ((euclidean__axioms.Col A B M) /\ (euclidean__axioms.Col B M A))))) as H61.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder A M B H60).
----------------------------- destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
exact H68.
---------------------------- exact H61.
------------------ assert (euclidean__axioms.BetS c b P) as H52 by exact H36.
assert (* Cut *) (euclidean__axioms.BetS d M P) as H53.
------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry P M d H40).
------------------- assert (* Cut *) (~(euclidean__axioms.Col A B c)) as H54.
-------------------- intro H54.
assert (* Cut *) (euclidean__defs.Meet A B C D) as H55.
--------------------- exists c.
split.
---------------------- exact H6.
---------------------- split.
----------------------- exact H8.
----------------------- split.
------------------------ exact H54.
------------------------ exact H16.
--------------------- apply (@H22 H55).
-------------------- assert (* Cut *) (~(euclidean__axioms.Col A B d)) as H55.
--------------------- intro H55.
assert (* Cut *) (euclidean__defs.Meet A B C D) as H56.
---------------------- exists d.
split.
----------------------- exact H6.
----------------------- split.
------------------------ exact H8.
------------------------ split.
------------------------- exact H55.
------------------------- exact H18.
---------------------- apply (@H22 H56).
--------------------- assert (* Cut *) (euclidean__defs.OS c d A B) as H56.
---------------------- exists P.
exists b.
exists M.
split.
----------------------- exact H12.
----------------------- split.
------------------------ exact H51.
------------------------ split.
------------------------- exact H52.
------------------------- split.
-------------------------- exact H53.
-------------------------- split.
--------------------------- apply (@euclidean__tactics.nCol__notCol A B c H54).
--------------------------- apply (@euclidean__tactics.nCol__notCol A B d H55).
---------------------- assert (* Cut *) (~(euclidean__defs.Meet A B c d)) as H57.
----------------------- intro H57.
assert (exists R, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq c d) /\ ((euclidean__axioms.Col A B R) /\ (euclidean__axioms.Col c d R)))) as H58 by exact H57.
destruct H58 as [R H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
destruct H63 as [H64 H65].
assert (* Cut *) (euclidean__axioms.Col D c d) as H66.
------------------------ apply (@euclidean__tactics.not__nCol__Col D c d).
-------------------------intro H66.
apply (@euclidean__tactics.Col__nCol__False D c d H66).
--------------------------apply (@lemma__collinear4.lemma__collinear4 C D c d H16 H18 H8).


------------------------ assert (* Cut *) (euclidean__axioms.Col D C c) as H67.
------------------------- assert (* Cut *) ((euclidean__axioms.Col D C c) /\ ((euclidean__axioms.Col D c C) /\ ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C))))) as H67.
-------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D c H16).
-------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H68.
------------------------- assert (* Cut *) (euclidean__axioms.Col D C d) as H68.
-------------------------- assert (* Cut *) ((euclidean__axioms.Col D C d) /\ ((euclidean__axioms.Col D d C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C))))) as H68.
--------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D d H18).
--------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
exact H69.
-------------------------- assert (* Cut *) (euclidean__axioms.neq D C) as H69.
--------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C D H8).
--------------------------- assert (* Cut *) (euclidean__axioms.Col C c d) as H70.
---------------------------- apply (@euclidean__tactics.not__nCol__Col C c d).
-----------------------------intro H70.
apply (@euclidean__tactics.Col__nCol__False C c d H70).
------------------------------apply (@lemma__collinear4.lemma__collinear4 D C c d H67 H68 H69).


---------------------------- assert (* Cut *) (euclidean__axioms.Col c d C) as H71.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col c C d) /\ ((euclidean__axioms.Col c d C) /\ ((euclidean__axioms.Col d C c) /\ ((euclidean__axioms.Col C d c) /\ (euclidean__axioms.Col d c C))))) as H71.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C c d H70).
------------------------------ destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
destruct H75 as [H76 H77].
destruct H77 as [H78 H79].
exact H74.
----------------------------- assert (* Cut *) (euclidean__axioms.Col c d D) as H72.
------------------------------ assert (* Cut *) ((euclidean__axioms.Col c D d) /\ ((euclidean__axioms.Col c d D) /\ ((euclidean__axioms.Col d D c) /\ ((euclidean__axioms.Col D d c) /\ (euclidean__axioms.Col d c D))))) as H72.
------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D c d H66).
------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H75.
------------------------------ assert (* Cut *) (euclidean__axioms.Col C D R) as H73.
------------------------------- apply (@euclidean__tactics.not__nCol__Col C D R).
--------------------------------intro H73.
apply (@euclidean__tactics.Col__nCol__False C D R H73).
---------------------------------apply (@lemma__collinear5.lemma__collinear5 c d C D R H62 H71 H72 H65).


------------------------------- assert (* Cut *) (euclidean__defs.Meet A B C D) as H74.
-------------------------------- exists R.
split.
--------------------------------- exact H60.
--------------------------------- split.
---------------------------------- exact H8.
---------------------------------- split.
----------------------------------- exact H64.
----------------------------------- exact H73.
-------------------------------- apply (@H22 H74).
----------------------- assert (* Cut *) (euclidean__defs.TP A B c d) as H58.
------------------------ split.
------------------------- exact H6.
------------------------- split.
-------------------------- exact H20.
-------------------------- split.
--------------------------- exact H57.
--------------------------- exact H56.
------------------------ assert (* Cut *) (C = C) as H59.
------------------------- apply (@logic.eq__refl Point C).
------------------------- assert (* Cut *) (euclidean__axioms.Col C D C) as H60.
-------------------------- right.
left.
exact H59.
-------------------------- assert (* Cut *) (euclidean__axioms.Col c d C) as H61.
--------------------------- apply (@euclidean__tactics.not__nCol__Col c d C).
----------------------------intro H61.
apply (@euclidean__tactics.Col__nCol__False c d C H61).
-----------------------------apply (@lemma__collinear5.lemma__collinear5 C D c d C H8 H16 H18 H60).


--------------------------- assert (* Cut *) (~(~(euclidean__defs.TP A B C D))) as H62.
---------------------------- intro H62.
assert (* Cut *) (euclidean__axioms.neq D C) as H63.
----------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C D H8).
----------------------------- assert (* Cut *) (~(euclidean__axioms.neq C d)) as H64.
------------------------------ intro H64.
assert (* Cut *) (euclidean__defs.TP A B C d) as H65.
------------------------------- apply (@lemma__parallelcollinear.lemma__parallelcollinear A B C c d H58 H61 H64).
------------------------------- assert (* Cut *) (euclidean__defs.TP A B d C) as H66.
-------------------------------- assert (* Cut *) ((euclidean__defs.TP B A C d) /\ ((euclidean__defs.TP A B d C) /\ (euclidean__defs.TP B A d C))) as H66.
--------------------------------- apply (@lemma__tarskiparallelflip.lemma__tarskiparallelflip A B C d H65).
--------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
exact H69.
-------------------------------- assert (* Cut *) (euclidean__axioms.Col d C D) as H67.
--------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C d) /\ ((euclidean__axioms.Col D d C) /\ ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col C d D) /\ (euclidean__axioms.Col d D C))))) as H67.
---------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D d H18).
---------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H72.
--------------------------------- assert (* Cut *) (euclidean__defs.TP A B D C) as H68.
---------------------------------- apply (@lemma__parallelcollinear.lemma__parallelcollinear A B D d C H66 H67 H63).
---------------------------------- assert (* Cut *) (euclidean__defs.TP A B C D) as H69.
----------------------------------- assert (* Cut *) ((euclidean__defs.TP B A D C) /\ ((euclidean__defs.TP A B C D) /\ (euclidean__defs.TP B A C D))) as H69.
------------------------------------ apply (@lemma__tarskiparallelflip.lemma__tarskiparallelflip A B D C H68).
------------------------------------ destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H72.
----------------------------------- apply (@H37).
------------------------------------apply (@euclidean__tactics.not__nCol__Col a d P).
-------------------------------------intro H70.
apply (@H62 H69).


------------------------------ assert (* Cut *) (euclidean__defs.TP A B c C) as H65.
------------------------------- apply (@eq__ind__r euclidean__axioms.Point d (fun X => euclidean__defs.TP A B c X)) with (x := C).
-------------------------------- exact H58.
--------------------------------apply (@euclidean__tactics.NNPP (C = d) H64).

------------------------------- assert (* Cut *) (euclidean__axioms.Col c C D) as H66.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C c) /\ ((euclidean__axioms.Col D c C) /\ ((euclidean__axioms.Col c C D) /\ ((euclidean__axioms.Col C c D) /\ (euclidean__axioms.Col c D C))))) as H66.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D c H16).
--------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H71.
-------------------------------- assert (* Cut *) (euclidean__defs.TP A B D C) as H67.
--------------------------------- apply (@lemma__parallelcollinear.lemma__parallelcollinear A B D c C H65 H66 H63).
--------------------------------- assert (* Cut *) (euclidean__defs.TP A B C D) as H68.
---------------------------------- assert (* Cut *) ((euclidean__defs.TP B A D C) /\ ((euclidean__defs.TP A B C D) /\ (euclidean__defs.TP B A C D))) as H68.
----------------------------------- apply (@lemma__tarskiparallelflip.lemma__tarskiparallelflip A B D C H67).
----------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H71.
---------------------------------- apply (@H37).
-----------------------------------apply (@euclidean__tactics.not__nCol__Col a d P).
------------------------------------intro H69.
apply (@H62 H68).


---------------------------- apply (@euclidean__tactics.NNPP (euclidean__defs.TP A B C D)).
-----------------------------intro H63.
assert (* Cut *) (False) as H64.
------------------------------ apply (@H62 H63).
------------------------------ contradiction H64.

Qed.
