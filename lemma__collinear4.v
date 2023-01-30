Require Export euclidean__axioms.
Require Export euclidean__tactics.
Require Export lemma__3__5b.
Require Export lemma__3__6a.
Require Export lemma__3__6b.
Require Export lemma__3__7a.
Require Export lemma__3__7b.
Require Export lemma__collinearorder.
Require Export lemma__outerconnectivity.
Require Export logic.
Definition lemma__collinear4 : forall A B C D, (euclidean__axioms.Col A B C) -> ((euclidean__axioms.Col A B D) -> ((euclidean__axioms.neq A B) -> (euclidean__axioms.Col B C D))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
intro H0.
intro H1.
assert (* Cut *) (euclidean__axioms.Col B C D) as H2.
- assert (* Cut *) ((B = C) \/ ((B = D) \/ ((C = D) \/ ((A = C) \/ ((A = D) \/ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A D)))))))))) as H2.
-- apply (@euclidean__tactics.NNPP ((B = C) \/ ((B = D) \/ ((C = D) \/ ((A = C) \/ ((A = D) \/ ((~(B = C)) /\ ((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D)))))))))))).
---intro H2.
assert (* Cut *) ((B = C) -> False) as H3.
---- intro H3.
apply (@H2).
-----left.
exact H3.

---- assert (* Cut *) (((B = D) \/ ((C = D) \/ ((A = C) \/ ((A = D) \/ ((~(B = C)) /\ ((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D)))))))))) -> False) as H4.
----- intro H4.
apply (@H2).
------right.
exact H4.

----- assert (* Cut *) ((B = D) -> False) as H5.
------ intro H5.
apply (@H4).
-------left.
exact H5.

------ assert (* Cut *) (((C = D) \/ ((A = C) \/ ((A = D) \/ ((~(B = C)) /\ ((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D))))))))) -> False) as H6.
------- intro H6.
apply (@H4).
--------right.
exact H6.

------- assert (* Cut *) ((C = D) -> False) as H7.
-------- intro H7.
apply (@H6).
---------left.
exact H7.

-------- assert (* Cut *) (((A = C) \/ ((A = D) \/ ((~(B = C)) /\ ((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D)))))))) -> False) as H8.
--------- intro H8.
apply (@H6).
----------right.
exact H8.

--------- assert (* Cut *) ((A = C) -> False) as H9.
---------- intro H9.
apply (@H8).
-----------left.
exact H9.

---------- assert (* Cut *) (((A = D) \/ ((~(B = C)) /\ ((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D))))))) -> False) as H10.
----------- intro H10.
apply (@H8).
------------right.
exact H10.

----------- assert (* Cut *) ((A = D) -> False) as H11.
------------ intro H11.
apply (@H10).
-------------left.
exact H11.

------------ assert (* Cut *) (((~(B = C)) /\ ((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D)))))) -> False) as H12.
------------- intro H12.
apply (@H10).
--------------right.
exact H12.

------------- assert (* Cut *) ((~(B = C)) -> (((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D))))) -> False)) as H13.
-------------- intro H13.
intro H14.
apply (@H12).
---------------split.
---------------- exact H13.
---------------- exact H14.

-------------- assert (* Cut *) (((~(B = D)) /\ ((~(C = D)) /\ ((~(A = C)) /\ (~(A = D))))) -> False) as H14.
--------------- apply (@H13 H3).
--------------- assert (* Cut *) ((~(B = D)) -> (((~(C = D)) /\ ((~(A = C)) /\ (~(A = D)))) -> False)) as H15.
---------------- intro H15.
intro H16.
apply (@H14).
-----------------split.
------------------ exact H15.
------------------ exact H16.

---------------- assert (* Cut *) (((~(C = D)) /\ ((~(A = C)) /\ (~(A = D)))) -> False) as H16.
----------------- apply (@H15 H5).
----------------- assert (* Cut *) ((~(C = D)) -> (((~(A = C)) /\ (~(A = D))) -> False)) as H17.
------------------ intro H17.
intro H18.
apply (@H16).
-------------------split.
-------------------- exact H17.
-------------------- exact H18.

------------------ assert (* Cut *) (((~(A = C)) /\ (~(A = D))) -> False) as H18.
------------------- apply (@H17 H7).
------------------- assert (* Cut *) ((~(A = C)) -> ((~(A = D)) -> False)) as H19.
-------------------- intro H19.
intro H20.
apply (@H18).
---------------------split.
---------------------- exact H19.
---------------------- exact H20.

-------------------- assert (* Cut *) ((~(A = D)) -> False) as H20.
--------------------- apply (@H19 H9).
--------------------- assert (* Cut *) (False) as H21.
---------------------- apply (@H20 H11).
---------------------- contradiction H21.

-- assert ((B = C) \/ ((B = D) \/ ((C = D) \/ ((A = C) \/ ((A = D) \/ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A D)))))))))) as H3 by exact H2.
assert ((B = C) \/ ((B = D) \/ ((C = D) \/ ((A = C) \/ ((A = D) \/ ((euclidean__axioms.neq B C) /\ ((euclidean__axioms.neq B D) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq A C) /\ (euclidean__axioms.neq A D)))))))))) as __TmpHyp by exact H3.
destruct __TmpHyp as [H4|H4].
--- assert (* Cut *) (euclidean__axioms.Col B C D) as H5.
---- left.
exact H4.
---- exact H5.
--- destruct H4 as [H5|H5].
---- assert (* Cut *) (euclidean__axioms.Col B C D) as H6.
----- right.
left.
exact H5.
----- exact H6.
---- destruct H5 as [H6|H6].
----- assert (* Cut *) (euclidean__axioms.Col B C D) as H7.
------ right.
right.
left.
exact H6.
------ exact H7.
----- destruct H6 as [H7|H7].
------ assert (* Cut *) (euclidean__axioms.Col C B D) as H8.
------- apply (@eq__ind__r euclidean__axioms.Point C (fun A0 => (euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Col A0 B D) -> ((euclidean__axioms.neq A0 B) -> (euclidean__axioms.Col C B D))))) with (x := A).
--------intro H8.
intro H9.
intro H10.
exact H9.

-------- exact H7.
-------- exact H.
-------- exact H0.
-------- exact H1.
------- assert (* Cut *) (euclidean__axioms.Col B C D) as H9.
-------- assert (* Cut *) ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C D B) /\ (euclidean__axioms.Col D B C))))) as H9.
--------- apply (@lemma__collinearorder.lemma__collinearorder C B D H8).
--------- destruct H9 as [H10 H11].
destruct H11 as [H12 H13].
destruct H13 as [H14 H15].
destruct H15 as [H16 H17].
exact H10.
-------- exact H9.
------ destruct H7 as [H8|H8].
------- assert (* Cut *) (euclidean__axioms.Col D B C) as H9.
-------- apply (@eq__ind__r euclidean__axioms.Point D (fun A0 => (euclidean__axioms.Col A0 B C) -> ((euclidean__axioms.Col A0 B D) -> ((euclidean__axioms.neq A0 B) -> (euclidean__axioms.Col D B C))))) with (x := A).
---------intro H9.
intro H10.
intro H11.
exact H9.

--------- exact H8.
--------- exact H.
--------- exact H0.
--------- exact H1.
-------- assert (* Cut *) (euclidean__axioms.Col B C D) as H10.
--------- assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H10.
---------- apply (@lemma__collinearorder.lemma__collinearorder D B C H9).
---------- destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
exact H13.
--------- exact H10.
------- assert (* Cut *) ((A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))))) as H9.
-------- destruct H8 as [H9 H10].
destruct H10 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
exact H.
-------- assert (* Cut *) (euclidean__axioms.Col B C D) as H10.
--------- assert (* Cut *) ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) as H10.
---------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)))).
-----------intro H10.
destruct H8 as [H11 H12].
destruct H12 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H9 as [H19|H19].
------------ assert (* Cut *) (False) as H20.
------------- apply (@H1 H19).
------------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H21.
-------------- intro H21.
apply (@H10).
---------------left.
exact H21.

-------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H22.
--------------- intro H22.
apply (@H10).
----------------right.
exact H22.

--------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H23.
---------------- intro H23.
apply (@H22).
-----------------left.
exact H23.

---------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H24.
----------------- intro H24.
apply (@H22).
------------------right.
exact H24.

----------------- contradiction H20.
------------ destruct H19 as [H20|H20].
------------- assert (* Cut *) (False) as H21.
-------------- apply (@H17 H20).
-------------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H22.
--------------- intro H22.
apply (@H10).
----------------left.
exact H22.

--------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H23.
---------------- intro H23.
apply (@H10).
-----------------right.
exact H23.

---------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H24.
----------------- intro H24.
apply (@H23).
------------------left.
exact H24.

----------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H25.
------------------ intro H25.
apply (@H23).
-------------------right.
exact H25.

------------------ contradiction H21.
------------- destruct H20 as [H21|H21].
-------------- assert (* Cut *) (False) as H22.
--------------- apply (@H11 H21).
--------------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H23.
---------------- intro H23.
apply (@H10).
-----------------left.
exact H23.

---------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H24.
----------------- intro H24.
apply (@H10).
------------------right.
exact H24.

----------------- assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H25.
------------------ intro H25.
apply (@H24).
-------------------left.
exact H25.

------------------ assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H26.
------------------- intro H26.
apply (@H24).
--------------------right.
exact H26.

------------------- contradiction H22.
-------------- destruct H21 as [H22|H22].
--------------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H23.
---------------- intro H23.
apply (@H10).
-----------------left.
exact H23.

---------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H24.
----------------- intro H24.
apply (@H10).
------------------right.
exact H24.

----------------- assert (* Cut *) (False) as H25.
------------------ apply (@H23 H22).
------------------ assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H26.
------------------- intro H26.
apply (@H24).
--------------------left.
exact H26.

------------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H27.
-------------------- intro H27.
apply (@H24).
---------------------right.
exact H27.

-------------------- contradiction H25.
--------------- destruct H22 as [H23|H23].
---------------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H24.
----------------- intro H24.
apply (@H10).
------------------left.
exact H24.

----------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H25.
------------------ intro H25.
apply (@H10).
-------------------right.
exact H25.

------------------ assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H26.
------------------- intro H26.
apply (@H25).
--------------------left.
exact H26.

------------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H27.
-------------------- intro H27.
apply (@H25).
---------------------right.
exact H27.

-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H26 H23).
--------------------- contradiction H28.
---------------- assert (* Cut *) ((euclidean__axioms.BetS B A C) -> False) as H24.
----------------- intro H24.
apply (@H10).
------------------left.
exact H24.

----------------- assert (* Cut *) (((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B)) -> False) as H25.
------------------ intro H25.
apply (@H10).
-------------------right.
exact H25.

------------------ assert (* Cut *) ((euclidean__axioms.BetS A B C) -> False) as H26.
------------------- intro H26.
apply (@H25).
--------------------left.
exact H26.

------------------- assert (* Cut *) ((euclidean__axioms.BetS A C B) -> False) as H27.
-------------------- intro H27.
apply (@H25).
---------------------right.
exact H27.

-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H27 H23).
--------------------- contradiction H28.

---------- assert ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) as H11 by exact H10.
assert ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))) as __TmpHyp0 by exact H11.
destruct __TmpHyp0 as [H12|H12].
----------- assert (* Cut *) ((A = B) \/ ((A = D) \/ ((B = D) \/ ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)))))) as H13.
------------ destruct H8 as [H13 H14].
destruct H14 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
exact H0.
------------ assert (* Cut *) (euclidean__axioms.Col B C D) as H14.
------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as H14.
-------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)))).
---------------intro H14.
destruct H8 as [H15 H16].
destruct H16 as [H17 H18].
destruct H18 as [H19 H20].
destruct H20 as [H21 H22].
destruct H9 as [H23|H23].
---------------- destruct H13 as [H24|H24].
----------------- assert (* Cut *) (False) as H25.
------------------ apply (@H1 H23).
------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H26.
------------------- intro H26.
apply (@H14).
--------------------left.
exact H26.

------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H27.
-------------------- intro H27.
apply (@H14).
---------------------right.
exact H27.

-------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H28.
--------------------- intro H28.
apply (@H27).
----------------------left.
exact H28.

--------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H29.
---------------------- intro H29.
apply (@H27).
-----------------------right.
exact H29.

---------------------- contradiction H25.
----------------- destruct H24 as [H25|H25].
------------------ assert (* Cut *) (False) as H26.
------------------- apply (@H1 H23).
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H22 H25).
-------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H28.
--------------------- intro H28.
apply (@H14).
----------------------left.
exact H28.

--------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------right.
exact H29.

---------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H30.
----------------------- intro H30.
apply (@H29).
------------------------left.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H31.
------------------------ intro H31.
apply (@H29).
-------------------------right.
exact H31.

------------------------ contradiction H27.
------------------ destruct H25 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H1 H23).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H17 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H1 H23).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------right.
exact H30.

----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H29 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H30).
---------------------------right.
exact H33.

-------------------------- contradiction H31.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H23).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H28).
--------------------------- contradiction H34.
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H23).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H33 H28).
--------------------------- contradiction H34.
---------------- destruct H13 as [H24|H24].
----------------- destruct H23 as [H25|H25].
------------------ assert (* Cut *) (False) as H26.
------------------- apply (@H1 H24).
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H21 H25).
-------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H28.
--------------------- intro H28.
apply (@H14).
----------------------left.
exact H28.

--------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------right.
exact H29.

---------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H30.
----------------------- intro H30.
apply (@H29).
------------------------left.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H31.
------------------------ intro H31.
apply (@H29).
-------------------------right.
exact H31.

------------------------ contradiction H27.
------------------ destruct H25 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H1 H24).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H15 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H1 H24).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H24).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H24).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
----------------- destruct H23 as [H25|H25].
------------------ destruct H24 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H21 H25).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H22 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H14).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H21 H25).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H17 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H21 H25).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H30 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H31).
----------------------------right.
exact H34.

--------------------------- contradiction H32.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H21 H25).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H29).
---------------------------- contradiction H35.
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H21 H25).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H34 H29).
---------------------------- contradiction H35.
------------------ destruct H24 as [H26|H26].
------------------- destruct H25 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H22 H26).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H15 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H22 H26).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H14).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H22 H26).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H22 H26).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
------------------- destruct H25 as [H27|H27].
-------------------- destruct H26 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H15 H27).
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H17 H28).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H15 H27).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) (False) as H33.
-------------------------- apply (@H31 H29).
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H32).
-----------------------------right.
exact H35.

---------------------------- contradiction H33.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H15 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H34 H30).
----------------------------- contradiction H36.
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H15 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H35 H30).
----------------------------- contradiction H36.
-------------------- destruct H26 as [H28|H28].
--------------------- destruct H27 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H17 H28).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H17 H28).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H17 H28).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
--------------------- destruct H27 as [H29|H29].
---------------------- destruct H28 as [H30|H30].
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H14).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) (False) as H33.
-------------------------- apply (@H31 H30).
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H32).
-----------------------------right.
exact H35.

---------------------------- contradiction H33.
----------------------- destruct H30 as [H31|H31].
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H34 H31).
----------------------------- contradiction H36.
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H35 H31).
----------------------------- contradiction H36.
---------------------- destruct H28 as [H30|H30].
----------------------- destruct H29 as [H31|H31].
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H30).
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H33).
------------------------------right.
exact H36.

----------------------------- contradiction H34.
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H14).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H30).
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H33).
------------------------------right.
exact H36.

----------------------------- contradiction H34.
----------------------- destruct H29 as [H31|H31].
------------------------ destruct H30 as [H32|H32].
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H14).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H35 H32).
------------------------------ contradiction H37.
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H14).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H36 H32).
------------------------------ contradiction H37.
------------------------ destruct H30 as [H32|H32].
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H14).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H35 H32).
------------------------------ contradiction H37.
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H14).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H14).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H36 H32).
------------------------------ contradiction H37.

-------------- assert ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as H15 by exact H14.
assert ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as __TmpHyp1 by exact H15.
destruct __TmpHyp1 as [H16|H16].
--------------- assert (* Cut *) (~(euclidean__axioms.nCol B C D)) as H17.
---------------- intro H17.
assert (* Cut *) (~(euclidean__axioms.BetS B C D)) as H18.
----------------- intro H18.
assert (* Cut *) (euclidean__axioms.Col B C D) as H19.
------------------ right.
right.
right.
right.
left.
exact H18.
------------------ apply (@euclidean__tactics.Col__nCol__False B C D H17 H19).
----------------- assert (* Cut *) (~(euclidean__axioms.BetS A C D)) as H19.
------------------ intro H19.
assert (* Cut *) (euclidean__axioms.BetS B C D) as H20.
------------------- destruct H8 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
apply (@lemma__3__5b.lemma__3__5b B A C D H16 H19).
------------------- apply (@H18 H20).
------------------ assert (* Cut *) (~(euclidean__axioms.nCol B D C)) as H20.
------------------- intro H20.
assert (* Cut *) (~(euclidean__axioms.BetS C D C)) as H21.
-------------------- destruct H8 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
apply (@euclidean__axioms.axiom__betweennessidentity C D).
-------------------- assert (* Cut *) (~(euclidean__axioms.BetS A D C)) as H22.
--------------------- intro H22.
assert (* Cut *) (euclidean__axioms.BetS B D C) as H23.
---------------------- destruct H8 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
apply (@lemma__3__5b.lemma__3__5b B A D C H12 H22).
---------------------- assert (* Cut *) (euclidean__axioms.Col B D C) as H24.
----------------------- right.
right.
right.
right.
left.
exact H23.
----------------------- apply (@euclidean__tactics.Col__nCol__False B D C H20 H24).
--------------------- assert (* Cut *) (C = D) as H23.
---------------------- destruct H8 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
apply (@lemma__outerconnectivity.lemma__outerconnectivity B A C D H12 H16 H19 H22).
---------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H24.
----------------------- right.
right.
left.
exact H23.
----------------------- assert (* Cut *) (euclidean__axioms.Col B D C) as H25.
------------------------ destruct H8 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
assert (* Cut *) ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col B D C) /\ (euclidean__axioms.Col D C B))))) as H33.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder B C D H24).
------------------------- destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
exact H40.
------------------------ apply (@euclidean__tactics.Col__nCol__False B D C H20 H25).
------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- assert (* Cut *) (euclidean__axioms.Col B D C) as H21.
--------------------- apply (@euclidean__tactics.not__nCol__Col B D C H20).
--------------------- destruct H8 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H30.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B D C H21).
---------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
-------------------- apply (@H20).
---------------------apply (@euclidean__tactics.nCol__notCol B D C).
----------------------intro H22.
apply (@euclidean__tactics.Col__nCol__False B C D H17 H21).


---------------- apply (@euclidean__tactics.not__nCol__Col B C D H17).
--------------- destruct H16 as [H17|H17].
---------------- assert (* Cut *) (euclidean__axioms.BetS D B A) as H18.
----------------- destruct H8 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
apply (@euclidean__axioms.axiom__betweennesssymmetry A B D H17).
----------------- assert (* Cut *) (euclidean__axioms.BetS D B C) as H19.
------------------ destruct H8 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
apply (@lemma__3__7b.lemma__3__7b D B A C H18 H12).
------------------ assert (* Cut *) (euclidean__axioms.Col D B C) as H20.
------------------- right.
right.
right.
right.
left.
exact H19.
------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- destruct H8 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H29.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder D B C H20).
--------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H32.
-------------------- exact H21.
---------------- assert (* Cut *) (euclidean__axioms.BetS B D A) as H18.
----------------- destruct H8 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
apply (@euclidean__axioms.axiom__betweennesssymmetry A D B H17).
----------------- assert (* Cut *) (euclidean__axioms.BetS B D C) as H19.
------------------ destruct H8 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
apply (@lemma__3__6b.lemma__3__6b B D A C H18 H12).
------------------ assert (* Cut *) (euclidean__axioms.Col B D C) as H20.
------------------- right.
right.
right.
right.
left.
exact H19.
------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- destruct H8 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H29.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder B D C H20).
--------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H36.
-------------------- exact H21.
------------- exact H14.
----------- destruct H12 as [H13|H13].
------------ assert (* Cut *) ((A = B) \/ ((A = D) \/ ((B = D) \/ ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)))))) as H14.
------------- destruct H8 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H0.
------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as H15.
--------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)))).
----------------intro H15.
destruct H8 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H9 as [H24|H24].
----------------- destruct H14 as [H25|H25].
------------------ assert (* Cut *) (False) as H26.
------------------- apply (@H1 H24).
------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H27.
-------------------- intro H27.
apply (@H15).
---------------------left.
exact H27.

-------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H28.
--------------------- intro H28.
apply (@H15).
----------------------right.
exact H28.

--------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H29.
---------------------- intro H29.
apply (@H28).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H30.
----------------------- intro H30.
apply (@H28).
------------------------right.
exact H30.

----------------------- contradiction H26.
------------------ destruct H25 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H1 H24).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H23 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H15).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H1 H24).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H18 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H24).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H30 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H31).
----------------------------right.
exact H34.

--------------------------- contradiction H32.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H24).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H29).
---------------------------- contradiction H35.
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H24).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H34 H29).
---------------------------- contradiction H35.
----------------- destruct H14 as [H25|H25].
------------------ destruct H24 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H1 H25).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H22 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H15).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H1 H25).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H16 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H25).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H25).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H25).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
------------------ destruct H24 as [H26|H26].
------------------- destruct H25 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H22 H26).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H23 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H22 H26).
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H18 H28).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H22 H26).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) (False) as H33.
-------------------------- apply (@H31 H29).
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H32).
-----------------------------right.
exact H35.

---------------------------- contradiction H33.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H22 H26).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H34 H30).
----------------------------- contradiction H36.
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H22 H26).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H35 H30).
----------------------------- contradiction H36.
------------------- destruct H25 as [H27|H27].
-------------------- destruct H26 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H23 H27).
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H16 H28).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H23 H27).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H23 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H23 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
-------------------- destruct H26 as [H28|H28].
--------------------- destruct H27 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H16 H28).
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H18 H29).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H16 H28).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H30).
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H33).
------------------------------right.
exact H36.

----------------------------- contradiction H34.
----------------------- destruct H30 as [H31|H31].
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H16 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H35 H31).
------------------------------ contradiction H37.
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H16 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H36 H31).
------------------------------ contradiction H37.
--------------------- destruct H27 as [H29|H29].
---------------------- destruct H28 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H18 H29).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
----------------------- destruct H30 as [H31|H31].
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H18 H29).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- contradiction H32.
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H18 H29).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- contradiction H32.
---------------------- destruct H28 as [H30|H30].
----------------------- destruct H29 as [H31|H31].
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H31).
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H33).
------------------------------right.
exact H36.

----------------------------- contradiction H34.
------------------------ destruct H31 as [H32|H32].
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H35 H32).
------------------------------ contradiction H37.
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H36 H32).
------------------------------ contradiction H37.
----------------------- destruct H29 as [H31|H31].
------------------------ destruct H30 as [H32|H32].
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H31).
---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H34).
-------------------------------right.
exact H37.

------------------------------ contradiction H35.
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H31).
---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H34).
-------------------------------right.
exact H37.

------------------------------ contradiction H35.
------------------------ destruct H30 as [H32|H32].
------------------------- destruct H31 as [H33|H33].
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H36 H33).
------------------------------- contradiction H38.
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H37 H33).
------------------------------- contradiction H38.
------------------------- destruct H31 as [H33|H33].
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H36 H33).
------------------------------- contradiction H38.
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H37 H33).
------------------------------- contradiction H38.

--------------- assert ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as H16 by exact H15.
assert ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as __TmpHyp1 by exact H16.
destruct __TmpHyp1 as [H17|H17].
---------------- assert (* Cut *) (euclidean__axioms.BetS D A B) as H18.
----------------- destruct H8 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
apply (@euclidean__axioms.axiom__betweennesssymmetry B A D H17).
----------------- assert (* Cut *) (euclidean__axioms.BetS D B C) as H19.
------------------ destruct H8 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
apply (@lemma__3__7a.lemma__3__7a D A B C H18 H13).
------------------ assert (* Cut *) (euclidean__axioms.Col D B C) as H20.
------------------- right.
right.
right.
right.
left.
exact H19.
------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- destruct H8 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H29.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder D B C H20).
--------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H32.
-------------------- exact H21.
---------------- destruct H17 as [H18|H18].
----------------- assert (* Cut *) (~(euclidean__axioms.nCol B C D)) as H19.
------------------ intro H19.
assert (* Cut *) (~(euclidean__axioms.BetS B C D)) as H20.
------------------- intro H20.
assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- right.
right.
right.
right.
left.
exact H20.
-------------------- apply (@euclidean__tactics.Col__nCol__False B C D H19 H21).
------------------- assert (* Cut *) (~(euclidean__axioms.BetS B D C)) as H21.
-------------------- intro H21.
assert (* Cut *) (euclidean__axioms.Col B D C) as H22.
--------------------- right.
right.
right.
right.
left.
exact H21.
--------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H23.
---------------------- destruct H8 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H31.
----------------------- apply (@lemma__collinearorder.lemma__collinearorder B D C H22).
----------------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
destruct H37 as [H38 H39].
exact H38.
---------------------- apply (@euclidean__tactics.Col__nCol__False B C D H19 H23).
-------------------- assert (* Cut *) (C = D) as H22.
--------------------- destruct H8 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
apply (@lemma__outerconnectivity.lemma__outerconnectivity A B C D H13 H18 H20 H21).
--------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H23.
---------------------- right.
right.
left.
exact H22.
---------------------- apply (@euclidean__tactics.Col__nCol__False B C D H19 H23).
------------------ apply (@euclidean__tactics.not__nCol__Col B C D H19).
----------------- assert (* Cut *) (euclidean__axioms.BetS D B C) as H19.
------------------ destruct H8 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
apply (@lemma__3__6a.lemma__3__6a A D B C H18 H13).
------------------ assert (* Cut *) (euclidean__axioms.Col D B C) as H20.
------------------- right.
right.
right.
right.
left.
exact H19.
------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- destruct H8 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
assert (* Cut *) ((euclidean__axioms.Col B D C) /\ ((euclidean__axioms.Col B C D) /\ ((euclidean__axioms.Col C D B) /\ ((euclidean__axioms.Col D C B) /\ (euclidean__axioms.Col C B D))))) as H29.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder D B C H20).
--------------------- destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
destruct H35 as [H36 H37].
exact H32.
-------------------- exact H21.
-------------- exact H15.
------------ assert (* Cut *) ((A = B) \/ ((A = D) \/ ((B = D) \/ ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)))))) as H14.
------------- destruct H8 as [H14 H15].
destruct H15 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
exact H0.
------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H15.
-------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as H15.
--------------- apply (@euclidean__tactics.NNPP ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)))).
----------------intro H15.
destruct H8 as [H16 H17].
destruct H17 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H9 as [H24|H24].
----------------- destruct H14 as [H25|H25].
------------------ assert (* Cut *) (False) as H26.
------------------- apply (@H1 H24).
------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H27.
-------------------- intro H27.
apply (@H15).
---------------------left.
exact H27.

-------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H28.
--------------------- intro H28.
apply (@H15).
----------------------right.
exact H28.

--------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H29.
---------------------- intro H29.
apply (@H28).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H30.
----------------------- intro H30.
apply (@H28).
------------------------right.
exact H30.

----------------------- contradiction H26.
------------------ destruct H25 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H1 H24).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H23 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H15).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H1 H24).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H18 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H24).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H30 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H31).
----------------------------right.
exact H34.

--------------------------- contradiction H32.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H24).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H29).
---------------------------- contradiction H35.
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H24).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H34 H29).
---------------------------- contradiction H35.
----------------- destruct H14 as [H25|H25].
------------------ destruct H24 as [H26|H26].
------------------- assert (* Cut *) (False) as H27.
-------------------- apply (@H1 H25).
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H22 H26).
--------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H29.
---------------------- intro H29.
apply (@H15).
-----------------------left.
exact H29.

---------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------right.
exact H30.

----------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H31.
------------------------ intro H31.
apply (@H30).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H32.
------------------------- intro H32.
apply (@H30).
--------------------------right.
exact H32.

------------------------- contradiction H28.
------------------- destruct H26 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H1 H25).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H16 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H1 H25).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H25).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H1 H25).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
------------------ destruct H24 as [H26|H26].
------------------- destruct H25 as [H27|H27].
-------------------- assert (* Cut *) (False) as H28.
--------------------- apply (@H22 H26).
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H23 H27).
---------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H30.
----------------------- intro H30.
apply (@H15).
------------------------left.
exact H30.

----------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------right.
exact H31.

------------------------ assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H32.
------------------------- intro H32.
apply (@H31).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H33.
-------------------------- intro H33.
apply (@H31).
---------------------------right.
exact H33.

-------------------------- contradiction H29.
-------------------- destruct H27 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H22 H26).
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H18 H28).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H22 H26).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) (False) as H33.
-------------------------- apply (@H31 H29).
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H32).
-----------------------------right.
exact H35.

---------------------------- contradiction H33.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H22 H26).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H34 H30).
----------------------------- contradiction H36.
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H22 H26).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) (False) as H36.
----------------------------- apply (@H35 H30).
----------------------------- contradiction H36.
------------------- destruct H25 as [H27|H27].
-------------------- destruct H26 as [H28|H28].
--------------------- assert (* Cut *) (False) as H29.
---------------------- apply (@H23 H27).
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H16 H28).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
--------------------- destruct H28 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H23 H27).
----------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H31.
------------------------ intro H31.
apply (@H15).
-------------------------left.
exact H31.

------------------------ assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------right.
exact H32.

------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H33.
-------------------------- intro H33.
apply (@H32).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H34.
--------------------------- intro H34.
apply (@H32).
----------------------------right.
exact H34.

--------------------------- contradiction H30.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H23 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H23 H27).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
-------------------- destruct H26 as [H28|H28].
--------------------- destruct H27 as [H29|H29].
---------------------- assert (* Cut *) (False) as H30.
----------------------- apply (@H16 H28).
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H18 H29).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
---------------------- destruct H29 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H16 H28).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H30).
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H33).
------------------------------right.
exact H36.

----------------------------- contradiction H34.
----------------------- destruct H30 as [H31|H31].
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H16 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H35 H31).
------------------------------ contradiction H37.
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H16 H28).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H36 H31).
------------------------------ contradiction H37.
--------------------- destruct H27 as [H29|H29].
---------------------- destruct H28 as [H30|H30].
----------------------- assert (* Cut *) (False) as H31.
------------------------ apply (@H18 H29).
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H34.
--------------------------- intro H34.
apply (@H33).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------right.
exact H35.

---------------------------- contradiction H31.
----------------------- destruct H30 as [H31|H31].
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H18 H29).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- contradiction H32.
------------------------ assert (* Cut *) (False) as H32.
------------------------- apply (@H18 H29).
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- contradiction H32.
---------------------- destruct H28 as [H30|H30].
----------------------- destruct H29 as [H31|H31].
------------------------ assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H32.
------------------------- intro H32.
apply (@H15).
--------------------------left.
exact H32.

------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------right.
exact H33.

-------------------------- assert (* Cut *) (False) as H34.
--------------------------- apply (@H32 H31).
--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H33).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H33).
------------------------------right.
exact H36.

----------------------------- contradiction H34.
------------------------ destruct H31 as [H32|H32].
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H35 H32).
------------------------------ contradiction H37.
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H35.
---------------------------- intro H35.
apply (@H34).
-----------------------------left.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------right.
exact H36.

----------------------------- assert (* Cut *) (False) as H37.
------------------------------ apply (@H36 H32).
------------------------------ contradiction H37.
----------------------- destruct H29 as [H31|H31].
------------------------ destruct H30 as [H32|H32].
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H31).
---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H34).
-------------------------------right.
exact H37.

------------------------------ contradiction H35.
------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H33.
-------------------------- intro H33.
apply (@H15).
---------------------------left.
exact H33.

-------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------right.
exact H34.

--------------------------- assert (* Cut *) (False) as H35.
---------------------------- apply (@H33 H31).
---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H34).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H34).
-------------------------------right.
exact H37.

------------------------------ contradiction H35.
------------------------ destruct H30 as [H32|H32].
------------------------- destruct H31 as [H33|H33].
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H36 H33).
------------------------------- contradiction H38.
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H37 H33).
------------------------------- contradiction H38.
------------------------- destruct H31 as [H33|H33].
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H36 H33).
------------------------------- contradiction H38.
-------------------------- assert (* Cut *) ((euclidean__axioms.BetS B A D) -> False) as H34.
--------------------------- intro H34.
apply (@H15).
----------------------------left.
exact H34.

--------------------------- assert (* Cut *) (((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B)) -> False) as H35.
---------------------------- intro H35.
apply (@H15).
-----------------------------right.
exact H35.

---------------------------- assert (* Cut *) ((euclidean__axioms.BetS A B D) -> False) as H36.
----------------------------- intro H36.
apply (@H35).
------------------------------left.
exact H36.

----------------------------- assert (* Cut *) ((euclidean__axioms.BetS A D B) -> False) as H37.
------------------------------ intro H37.
apply (@H35).
-------------------------------right.
exact H37.

------------------------------ assert (* Cut *) (False) as H38.
------------------------------- apply (@H37 H33).
------------------------------- contradiction H38.

--------------- assert ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as H16 by exact H15.
assert ((euclidean__axioms.BetS B A D) \/ ((euclidean__axioms.BetS A B D) \/ (euclidean__axioms.BetS A D B))) as __TmpHyp1 by exact H16.
destruct __TmpHyp1 as [H17|H17].
---------------- assert (* Cut *) (euclidean__axioms.BetS D A B) as H18.
----------------- destruct H8 as [H18 H19].
destruct H19 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
apply (@euclidean__axioms.axiom__betweennesssymmetry B A D H17).
----------------- assert (* Cut *) (euclidean__axioms.BetS D C B) as H19.
------------------ destruct H8 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
apply (@lemma__3__5b.lemma__3__5b D A C B H18 H13).
------------------ assert (* Cut *) (euclidean__axioms.BetS B C D) as H20.
------------------- destruct H8 as [H20 H21].
destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
apply (@euclidean__axioms.axiom__betweennesssymmetry D C B H19).
------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H21.
-------------------- right.
right.
right.
right.
left.
exact H20.
-------------------- exact H21.
---------------- destruct H17 as [H18|H18].
----------------- assert (* Cut *) (euclidean__axioms.BetS C B D) as H19.
------------------ destruct H8 as [H19 H20].
destruct H20 as [H21 H22].
destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
apply (@lemma__3__6a.lemma__3__6a A C B D H13 H18).
------------------ assert (* Cut *) (euclidean__axioms.Col B C D) as H20.
------------------- right.
right.
right.
left.
exact H19.
------------------- exact H20.
----------------- assert (* Cut *) (~(euclidean__axioms.nCol B C D)) as H19.
------------------ intro H19.
assert (* Cut *) (~(~(euclidean__axioms.BetS B D C))) as H20.
------------------- intro H20.
assert (* Cut *) (~(~(euclidean__axioms.BetS B C D))) as H21.
-------------------- intro H21.
assert (* Cut *) (euclidean__axioms.BetS B C A) as H22.
--------------------- destruct H8 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
apply (@euclidean__axioms.axiom__betweennesssymmetry A C B H13).
--------------------- assert (* Cut *) (euclidean__axioms.BetS B D A) as H23.
---------------------- destruct H8 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
apply (@euclidean__axioms.axiom__betweennesssymmetry A D B H18).
---------------------- assert (* Cut *) (C = D) as H24.
----------------------- destruct H8 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
apply (@euclidean__axioms.axiom__connectivity B C D A H22 H23 H21 H20).
----------------------- destruct H8 as [H25 H26].
destruct H19 as [H27 H28].
destruct H26 as [H29 H30].
destruct H28 as [H31 H32].
destruct H30 as [H33 H34].
destruct H32 as [H35 H36].
destruct H34 as [H37 H38].
destruct H36 as [H39 H40].
destruct H40 as [H41 H42].
destruct H9 as [H43|H43].
------------------------ destruct H14 as [H44|H44].
------------------------- apply (@H1 H44).
------------------------- destruct H44 as [H45|H45].
-------------------------- apply (@H1 H43).
-------------------------- destruct H45 as [H46|H46].
--------------------------- apply (@H1 H43).
--------------------------- destruct H46 as [H47|H47].
---------------------------- apply (@H1 H43).
---------------------------- destruct H47 as [H48|H48].
----------------------------- apply (@H1 H43).
----------------------------- apply (@H1 H43).
------------------------ destruct H14 as [H44|H44].
------------------------- destruct H43 as [H45|H45].
-------------------------- apply (@H1 H44).
-------------------------- destruct H45 as [H46|H46].
--------------------------- apply (@H1 H44).
--------------------------- destruct H46 as [H47|H47].
---------------------------- apply (@H1 H44).
---------------------------- destruct H47 as [H48|H48].
----------------------------- apply (@H1 H44).
----------------------------- apply (@H1 H44).
------------------------- destruct H43 as [H45|H45].
-------------------------- destruct H44 as [H46|H46].
--------------------------- apply (@H33 H24).
--------------------------- destruct H46 as [H47|H47].
---------------------------- apply (@H29 H47).
---------------------------- destruct H47 as [H48|H48].
----------------------------- apply (@H33 H24).
----------------------------- destruct H48 as [H49|H49].
------------------------------ apply (@H33 H24).
------------------------------ apply (@H33 H24).
-------------------------- destruct H44 as [H46|H46].
--------------------------- destruct H45 as [H47|H47].
---------------------------- apply (@H25 H47).
---------------------------- destruct H47 as [H48|H48].
----------------------------- apply (@H33 H24).
----------------------------- destruct H48 as [H49|H49].
------------------------------ apply (@H33 H24).
------------------------------ apply (@H33 H24).
--------------------------- destruct H45 as [H47|H47].
---------------------------- destruct H46 as [H48|H48].
----------------------------- apply (@H25 H47).
----------------------------- destruct H48 as [H49|H49].
------------------------------ apply (@H25 H47).
------------------------------ destruct H49 as [H50|H50].
------------------------------- apply (@H25 H47).
------------------------------- apply (@H25 H47).
---------------------------- destruct H46 as [H48|H48].
----------------------------- destruct H47 as [H49|H49].
------------------------------ apply (@H29 H48).
------------------------------ destruct H49 as [H50|H50].
------------------------------- apply (@H29 H48).
------------------------------- apply (@H29 H48).
----------------------------- destruct H47 as [H49|H49].
------------------------------ destruct H48 as [H50|H50].
------------------------------- apply (@H33 H24).
------------------------------- destruct H50 as [H51|H51].
-------------------------------- apply (@H33 H24).
-------------------------------- apply (@H33 H24).
------------------------------ destruct H48 as [H50|H50].
------------------------------- destruct H49 as [H51|H51].
-------------------------------- apply (@H33 H24).
-------------------------------- apply (@H33 H24).
------------------------------- destruct H49 as [H51|H51].
-------------------------------- destruct H50 as [H52|H52].
--------------------------------- apply (@H33 H24).
--------------------------------- apply (@H33 H24).
-------------------------------- destruct H50 as [H52|H52].
--------------------------------- apply (@H33 H24).
--------------------------------- apply (@H33 H24).
-------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H22.
--------------------- assert (* Cut *) (euclidean__axioms.BetS B C D) as H22.
---------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS B C D) H21).
---------------------- right.
right.
right.
right.
left.
exact H22.
--------------------- apply (@H21).
----------------------intro H23.
apply (@euclidean__tactics.Col__nCol__False B C D H19 H22).

------------------- assert (* Cut *) (euclidean__axioms.Col B D C) as H21.
-------------------- assert (* Cut *) (euclidean__axioms.BetS B D C) as H21.
--------------------- apply (@euclidean__tactics.NNPP (euclidean__axioms.BetS B D C) H20).
--------------------- right.
right.
right.
right.
left.
exact H21.
-------------------- assert (* Cut *) (euclidean__axioms.Col B C D) as H22.
--------------------- destruct H8 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
assert (* Cut *) ((euclidean__axioms.Col D B C) /\ ((euclidean__axioms.Col D C B) /\ ((euclidean__axioms.Col C B D) /\ ((euclidean__axioms.Col B C D) /\ (euclidean__axioms.Col C D B))))) as H30.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder B D C H21).
---------------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
--------------------- apply (@H20).
----------------------intro H23.
apply (@euclidean__tactics.Col__nCol__False B C D H19 H22).

------------------ apply (@euclidean__tactics.not__nCol__Col B C D H19).
-------------- exact H15.
--------- exact H10.
- exact H2.
Qed.
