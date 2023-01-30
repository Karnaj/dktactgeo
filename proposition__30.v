Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__30helper.
Require Export lemma__NCdistinct.
Require Export lemma__NChelper.
Require Export lemma__NCorder.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearbetween.
Require Export lemma__collinearorder.
Require Export lemma__collinearparallel.
Require Export lemma__crossimpliesopposite.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export lemma__oppositesidesymmetric.
Require Export lemma__parallelNC.
Require Export lemma__paralleldef2B.
Require Export lemma__parallelflip.
Require Export lemma__parallelsymmetric.
Require Export lemma__planeseparation.
Require Export lemma__samesidesymmetric.
Require Export logic.
Require Export proposition__30A.
Definition parnotmeet : forall A B C D, (euclidean__defs.Par A B C D) -> (~(euclidean__defs.Meet A B C D)).
Proof.
intro A.
intro B.
intro C.
intro D.
intro H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as H0 by exact H.
assert (exists U V u v X, (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.Col A B U) /\ ((euclidean__axioms.Col A B V) /\ ((euclidean__axioms.neq U V) /\ ((euclidean__axioms.Col C D u) /\ ((euclidean__axioms.Col C D v) /\ ((euclidean__axioms.neq u v) /\ ((~(euclidean__defs.Meet A B C D)) /\ ((euclidean__axioms.BetS U X v) /\ (euclidean__axioms.BetS u X V))))))))))) as __TmpHyp by exact H0.
destruct __TmpHyp as [x H1].
destruct H1 as [x0 H2].
destruct H2 as [x1 H3].
destruct H3 as [x2 H4].
destruct H4 as [x3 H5].
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
exact H22.
Qed.
Definition proposition__30 : forall A B C D E F G H K, (euclidean__defs.Par A B E F) -> ((euclidean__defs.Par C D E F) -> ((euclidean__axioms.BetS G H K) -> ((euclidean__axioms.Col A B G) -> ((euclidean__axioms.Col E F H) -> ((euclidean__axioms.Col C D K) -> ((euclidean__axioms.neq A G) -> ((euclidean__axioms.neq E H) -> ((euclidean__axioms.neq C K) -> (euclidean__defs.Par A B C D))))))))).
Proof.
intro A.
intro B.
intro C.
intro D.
intro E.
intro F.
intro G.
intro H.
intro K.
intro H0.
intro H1.
intro H2.
intro H3.
intro H4.
intro H5.
intro H6.
intro H7.
intro H8.
assert (* Cut *) (exists b, (euclidean__axioms.BetS A G b) /\ (euclidean__axioms.Cong G b A G)) as H9.
- apply (@lemma__extension.lemma__extension A G A G H6 H6).
- destruct H9 as [b H10].
destruct H10 as [H11 H12].
assert (* Cut *) (exists f, (euclidean__axioms.BetS E H f) /\ (euclidean__axioms.Cong H f E H)) as H13.
-- apply (@lemma__extension.lemma__extension E H E H H7 H7).
-- destruct H13 as [f H14].
destruct H14 as [H15 H16].
assert (* Cut *) (exists d, (euclidean__axioms.BetS C K d) /\ (euclidean__axioms.Cong K d C K)) as H17.
--- apply (@lemma__extension.lemma__extension C K C K H8 H8).
--- destruct H17 as [d H18].
destruct H18 as [H19 H20].
assert (* Cut *) (euclidean__axioms.nCol C D E) as H21.
---- assert (* Cut *) ((euclidean__axioms.nCol C D E) /\ ((euclidean__axioms.nCol C E F) /\ ((euclidean__axioms.nCol D E F) /\ (euclidean__axioms.nCol C D F)))) as H21.
----- apply (@lemma__parallelNC.lemma__parallelNC C D E F H1).
----- destruct H21 as [H22 H23].
destruct H23 as [H24 H25].
destruct H25 as [H26 H27].
exact H22.
---- assert (* Cut *) (euclidean__axioms.neq C D) as H22.
----- assert (* Cut *) ((euclidean__axioms.neq C D) /\ ((euclidean__axioms.neq D E) /\ ((euclidean__axioms.neq C E) /\ ((euclidean__axioms.neq D C) /\ ((euclidean__axioms.neq E D) /\ (euclidean__axioms.neq E C)))))) as H22.
------ apply (@lemma__NCdistinct.lemma__NCdistinct C D E H21).
------ destruct H22 as [H23 H24].
destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H23.
----- assert (* Cut *) (euclidean__axioms.Col A G b) as H23.
------ right.
right.
right.
right.
left.
exact H11.
------ assert (* Cut *) (euclidean__axioms.Col G A b) as H24.
------- assert (* Cut *) ((euclidean__axioms.Col G A b) /\ ((euclidean__axioms.Col G b A) /\ ((euclidean__axioms.Col b A G) /\ ((euclidean__axioms.Col A b G) /\ (euclidean__axioms.Col b G A))))) as H24.
-------- apply (@lemma__collinearorder.lemma__collinearorder A G b H23).
-------- destruct H24 as [H25 H26].
destruct H26 as [H27 H28].
destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
exact H25.
------- assert (* Cut *) (euclidean__axioms.Col G A B) as H25.
-------- assert (* Cut *) ((euclidean__axioms.Col B A G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G A B) /\ ((euclidean__axioms.Col A G B) /\ (euclidean__axioms.Col G B A))))) as H25.
--------- apply (@lemma__collinearorder.lemma__collinearorder A B G H3).
--------- destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
exact H30.
-------- assert (* Cut *) (euclidean__axioms.neq G A) as H26.
--------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A G H6).
--------- assert (* Cut *) (euclidean__axioms.Col A b B) as H27.
---------- apply (@euclidean__tactics.not__nCol__Col A b B).
-----------intro H27.
apply (@euclidean__tactics.Col__nCol__False A b B H27).
------------apply (@lemma__collinear4.lemma__collinear4 G A b B H24 H25 H26).


---------- assert (* Cut *) (euclidean__axioms.Col B A b) as H28.
----------- assert (* Cut *) ((euclidean__axioms.Col b A B) /\ ((euclidean__axioms.Col b B A) /\ ((euclidean__axioms.Col B A b) /\ ((euclidean__axioms.Col A B b) /\ (euclidean__axioms.Col B b A))))) as H28.
------------ apply (@lemma__collinearorder.lemma__collinearorder A b B H27).
------------ destruct H28 as [H29 H30].
destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
destruct H34 as [H35 H36].
exact H33.
----------- assert (* Cut *) (euclidean__defs.Par E F A B) as H29.
------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B E F H0).
------------ assert (* Cut *) (euclidean__defs.Par E F B A) as H30.
------------- assert (* Cut *) ((euclidean__defs.Par F E A B) /\ ((euclidean__defs.Par E F B A) /\ (euclidean__defs.Par F E B A))) as H30.
-------------- apply (@lemma__parallelflip.lemma__parallelflip E F A B H29).
-------------- destruct H30 as [H31 H32].
destruct H32 as [H33 H34].
exact H33.
------------- assert (* Cut *) (euclidean__axioms.neq A b) as H31.
-------------- assert (* Cut *) ((euclidean__axioms.neq G b) /\ ((euclidean__axioms.neq A G) /\ (euclidean__axioms.neq A b))) as H31.
--------------- apply (@lemma__betweennotequal.lemma__betweennotequal A G b H11).
--------------- destruct H31 as [H32 H33].
destruct H33 as [H34 H35].
exact H35.
-------------- assert (* Cut *) (euclidean__axioms.neq b A) as H32.
--------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric A b H31).
--------------- assert (* Cut *) (euclidean__defs.Par E F b A) as H33.
---------------- apply (@lemma__collinearparallel.lemma__collinearparallel E F b B A H30 H28 H32).
---------------- assert (* Cut *) (euclidean__defs.Par E F A b) as H34.
----------------- assert (* Cut *) ((euclidean__defs.Par F E b A) /\ ((euclidean__defs.Par E F A b) /\ (euclidean__defs.Par F E A b))) as H34.
------------------ apply (@lemma__parallelflip.lemma__parallelflip E F b A H33).
------------------ destruct H34 as [H35 H36].
destruct H36 as [H37 H38].
exact H37.
----------------- assert (* Cut *) (euclidean__defs.Par A b E F) as H35.
------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E F A b H34).
------------------ assert (* Cut *) (euclidean__axioms.Col E H f) as H36.
------------------- right.
right.
right.
right.
left.
exact H15.
------------------- assert (* Cut *) (euclidean__axioms.Col H E f) as H37.
-------------------- assert (* Cut *) ((euclidean__axioms.Col H E f) /\ ((euclidean__axioms.Col H f E) /\ ((euclidean__axioms.Col f E H) /\ ((euclidean__axioms.Col E f H) /\ (euclidean__axioms.Col f H E))))) as H37.
--------------------- apply (@lemma__collinearorder.lemma__collinearorder E H f H36).
--------------------- destruct H37 as [H38 H39].
destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
exact H38.
-------------------- assert (* Cut *) (euclidean__axioms.Col H E F) as H38.
--------------------- assert (* Cut *) ((euclidean__axioms.Col F E H) /\ ((euclidean__axioms.Col F H E) /\ ((euclidean__axioms.Col H E F) /\ ((euclidean__axioms.Col E H F) /\ (euclidean__axioms.Col H F E))))) as H38.
---------------------- apply (@lemma__collinearorder.lemma__collinearorder E F H H4).
---------------------- destruct H38 as [H39 H40].
destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H43.
--------------------- assert (* Cut *) (euclidean__axioms.neq H E) as H39.
---------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E H H7).
---------------------- assert (* Cut *) (euclidean__axioms.Col E f F) as H40.
----------------------- apply (@euclidean__tactics.not__nCol__Col E f F).
------------------------intro H40.
apply (@euclidean__tactics.Col__nCol__False E f F H40).
-------------------------apply (@lemma__collinear4.lemma__collinear4 H E f F H37 H38 H39).


----------------------- assert (* Cut *) (euclidean__axioms.Col F E f) as H41.
------------------------ assert (* Cut *) ((euclidean__axioms.Col f E F) /\ ((euclidean__axioms.Col f F E) /\ ((euclidean__axioms.Col F E f) /\ ((euclidean__axioms.Col E F f) /\ (euclidean__axioms.Col F f E))))) as H41.
------------------------- apply (@lemma__collinearorder.lemma__collinearorder E f F H40).
------------------------- destruct H41 as [H42 H43].
destruct H43 as [H44 H45].
destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
------------------------ assert (* Cut *) (euclidean__axioms.neq E f) as H42.
------------------------- assert (* Cut *) ((euclidean__axioms.neq H f) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E f))) as H42.
-------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H f H15).
-------------------------- destruct H42 as [H43 H44].
destruct H44 as [H45 H46].
exact H46.
------------------------- assert (* Cut *) (euclidean__axioms.neq f E) as H43.
-------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric E f H42).
-------------------------- assert (* Cut *) (euclidean__defs.Par A b F E) as H44.
--------------------------- assert (* Cut *) ((euclidean__defs.Par b A E F) /\ ((euclidean__defs.Par A b F E) /\ (euclidean__defs.Par b A F E))) as H44.
---------------------------- apply (@lemma__parallelflip.lemma__parallelflip A b E F H35).
---------------------------- destruct H44 as [H45 H46].
destruct H46 as [H47 H48].
exact H47.
--------------------------- assert (* Cut *) (euclidean__defs.Par A b f E) as H45.
---------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel A b f F E H44 H41 H43).
---------------------------- assert (* Cut *) (euclidean__defs.Par A b E f) as H46.
----------------------------- assert (* Cut *) ((euclidean__defs.Par b A f E) /\ ((euclidean__defs.Par A b E f) /\ (euclidean__defs.Par b A E f))) as H46.
------------------------------ apply (@lemma__parallelflip.lemma__parallelflip A b f E H45).
------------------------------ destruct H46 as [H47 H48].
destruct H48 as [H49 H50].
exact H49.
----------------------------- assert (* Cut *) (euclidean__axioms.Col C K d) as H47.
------------------------------ right.
right.
right.
right.
left.
exact H19.
------------------------------ assert (* Cut *) (euclidean__axioms.Col K C d) as H48.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col K C d) /\ ((euclidean__axioms.Col K d C) /\ ((euclidean__axioms.Col d C K) /\ ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col d K C))))) as H48.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C K d H47).
-------------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H49.
------------------------------- assert (* Cut *) (euclidean__axioms.Col K C D) as H49.
-------------------------------- assert (* Cut *) ((euclidean__axioms.Col D C K) /\ ((euclidean__axioms.Col D K C) /\ ((euclidean__axioms.Col K C D) /\ ((euclidean__axioms.Col C K D) /\ (euclidean__axioms.Col K D C))))) as H49.
--------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C D K H5).
--------------------------------- destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H54.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq K C) as H50.
--------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C K H8).
--------------------------------- assert (* Cut *) (euclidean__axioms.Col C d D) as H51.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col C d D).
-----------------------------------intro H51.
apply (@euclidean__tactics.Col__nCol__False C d D H51).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 K C d D H48 H49 H50).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col D C d) as H52.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col d C D) /\ ((euclidean__axioms.Col d D C) /\ ((euclidean__axioms.Col D C d) /\ ((euclidean__axioms.Col C D d) /\ (euclidean__axioms.Col D d C))))) as H52.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder C d D H51).
------------------------------------ destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
destruct H58 as [H59 H60].
exact H57.
----------------------------------- assert (* Cut *) (euclidean__defs.Par E F C D) as H53.
------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C D E F H1).
------------------------------------ assert (* Cut *) (euclidean__defs.Par E F D C) as H54.
------------------------------------- assert (* Cut *) ((euclidean__defs.Par F E C D) /\ ((euclidean__defs.Par E F D C) /\ (euclidean__defs.Par F E D C))) as H54.
-------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip E F C D H53).
-------------------------------------- destruct H54 as [H55 H56].
destruct H56 as [H57 H58].
exact H57.
------------------------------------- assert (* Cut *) (euclidean__axioms.neq C d) as H55.
-------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K d) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C d))) as H55.
--------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C K d H19).
--------------------------------------- destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H59.
-------------------------------------- assert (* Cut *) (euclidean__axioms.neq d C) as H56.
--------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C d H55).
--------------------------------------- assert (* Cut *) (euclidean__defs.Par E F d C) as H57.
---------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel E F d D C H54 H52 H56).
---------------------------------------- assert (* Cut *) (euclidean__defs.Par E F C d) as H58.
----------------------------------------- assert (* Cut *) ((euclidean__defs.Par F E d C) /\ ((euclidean__defs.Par E F C d) /\ (euclidean__defs.Par F E C d))) as H58.
------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip E F d C H57).
------------------------------------------ destruct H58 as [H59 H60].
destruct H60 as [H61 H62].
exact H61.
----------------------------------------- assert (* Cut *) (euclidean__defs.Par C d E F) as H59.
------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E F C d H58).
------------------------------------------ assert (* Cut *) (euclidean__defs.Par C d F E) as H60.
------------------------------------------- assert (* Cut *) ((euclidean__defs.Par d C E F) /\ ((euclidean__defs.Par C d F E) /\ (euclidean__defs.Par d C F E))) as H60.
-------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C d E F H59).
-------------------------------------------- destruct H60 as [H61 H62].
destruct H62 as [H63 H64].
exact H63.
------------------------------------------- assert (* Cut *) (euclidean__defs.Par C d f E) as H61.
-------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel C d f F E H60 H41 H43).
-------------------------------------------- assert (* Cut *) (euclidean__defs.Par C d E f) as H62.
--------------------------------------------- assert (* Cut *) ((euclidean__defs.Par d C f E) /\ ((euclidean__defs.Par C d E f) /\ (euclidean__defs.Par d C E f))) as H62.
---------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C d f E H61).
---------------------------------------------- destruct H62 as [H63 H64].
destruct H64 as [H65 H66].
exact H65.
--------------------------------------------- assert (* Cut *) (H = H) as H63.
---------------------------------------------- apply (@logic.eq__refl Point H).
---------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H H) as H64.
----------------------------------------------- right.
right.
left.
exact H63.
----------------------------------------------- assert (* Cut *) (euclidean__axioms.Col A b G) as H65.
------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A G b) /\ ((euclidean__axioms.Col A b G) /\ ((euclidean__axioms.Col b G A) /\ ((euclidean__axioms.Col G b A) /\ (euclidean__axioms.Col b A G))))) as H65.
------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G A b H24).
------------------------------------------------- destruct H65 as [H66 H67].
destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
exact H68.
------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col E f H) as H66.
------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H f) /\ ((euclidean__axioms.Col E f H) /\ ((euclidean__axioms.Col f H E) /\ ((euclidean__axioms.Col H f E) /\ (euclidean__axioms.Col f E H))))) as H66.
-------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H E f H37).
-------------------------------------------------- destruct H66 as [H67 H68].
destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
destruct H72 as [H73 H74].
exact H69.
------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col f E H) as H67.
-------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col f E H) /\ ((euclidean__axioms.Col f H E) /\ ((euclidean__axioms.Col H E f) /\ ((euclidean__axioms.Col E H f) /\ (euclidean__axioms.Col H f E))))) as H67.
--------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E f H H66).
--------------------------------------------------- destruct H67 as [H68 H69].
destruct H69 as [H70 H71].
destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H68.
-------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b f E) as H68.
--------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par d C E f) /\ ((euclidean__defs.Par C d f E) /\ (euclidean__defs.Par d C f E))) as H68.
---------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C d E f H62).
---------------------------------------------------- destruct H68 as [H69 H70].
destruct H70 as [H71 H72].
exact H45.
--------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b H E) as H69.
---------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel A b H f E H68 H67 H39).
---------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H E A b) as H70.
----------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A b H E H69).
----------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H b A) as H71.
------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par E H A b) /\ ((euclidean__defs.Par H E b A) /\ (euclidean__defs.Par E H b A))) as H71.
------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip H E A b H70).
------------------------------------------------------- destruct H71 as [H72 H73].
destruct H73 as [H74 H75].
exact H75.
------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col b A G) as H72.
------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col b A G) /\ ((euclidean__axioms.Col b G A) /\ ((euclidean__axioms.Col G A b) /\ ((euclidean__axioms.Col A G b) /\ (euclidean__axioms.Col G b A))))) as H72.
-------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A b G H65).
-------------------------------------------------------- destruct H72 as [H73 H74].
destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H73.
------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H G A) as H73.
-------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel E H G b A H71 H72 H26).
-------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H A G) as H74.
--------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H E G A) /\ ((euclidean__defs.Par E H A G) /\ (euclidean__defs.Par H E A G))) as H74.
---------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip E H G A H73).
---------------------------------------------------------- destruct H74 as [H75 H76].
destruct H76 as [H77 H78].
exact H77.
--------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A G E H) as H75.
---------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E H A G H74).
---------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C d f E) as H76.
----------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par G A E H) /\ ((euclidean__defs.Par A G H E) /\ (euclidean__defs.Par G A H E))) as H76.
------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip A G E H H75).
------------------------------------------------------------ destruct H76 as [H77 H78].
destruct H78 as [H79 H80].
exact H61.
----------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col f E H) as H77.
------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A b G) /\ ((euclidean__axioms.Col A G b) /\ ((euclidean__axioms.Col G b A) /\ ((euclidean__axioms.Col b G A) /\ (euclidean__axioms.Col G A b))))) as H77.
------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder b A G H72).
------------------------------------------------------------- destruct H77 as [H78 H79].
destruct H79 as [H80 H81].
destruct H81 as [H82 H83].
destruct H83 as [H84 H85].
exact H67.
------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par C d H E) as H78.
------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel C d H f E H76 H77 H39).
------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H E C d) as H79.
-------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C d H E H78).
-------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par H E d C) as H80.
--------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E H C d) /\ ((euclidean__defs.Par H E d C) /\ (euclidean__defs.Par E H d C))) as H80.
---------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip H E C d H79).
---------------------------------------------------------------- destruct H80 as [H81 H82].
destruct H82 as [H83 H84].
exact H83.
--------------------------------------------------------------- assert (euclidean__axioms.Col C K d) as H81 by exact H47.
assert (* Cut *) (euclidean__axioms.Col d C K) as H82.
---------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col K C d) /\ ((euclidean__axioms.Col K d C) /\ ((euclidean__axioms.Col d C K) /\ ((euclidean__axioms.Col C d K) /\ (euclidean__axioms.Col d K C))))) as H82.
----------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder C K d H81).
----------------------------------------------------------------- destruct H82 as [H83 H84].
destruct H84 as [H85 H86].
destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H87.
---------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq C K) as H83.
----------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq K d) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C d))) as H83.
------------------------------------------------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal C K d H19).
------------------------------------------------------------------ destruct H83 as [H84 H85].
destruct H85 as [H86 H87].
exact H86.
----------------------------------------------------------------- assert (euclidean__axioms.neq K C) as H84 by exact H50.
assert (* Cut *) (euclidean__defs.Par H E K C) as H85.
------------------------------------------------------------------ apply (@lemma__collinearparallel.lemma__collinearparallel H E K d C H80 H82 H84).
------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par E H C K) as H86.
------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par E H K C) /\ ((euclidean__defs.Par H E C K) /\ (euclidean__defs.Par E H C K))) as H86.
-------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip H E K C H85).
-------------------------------------------------------------------- destruct H86 as [H87 H88].
destruct H88 as [H89 H90].
exact H90.
------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP E H C K) as H87.
-------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B E H C K H86).
-------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C K E H) as H88.
--------------------------------------------------------------------- destruct H87 as [H88 H89].
destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
exact H93.
--------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E H K) as H89.
---------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E H C) /\ ((euclidean__axioms.nCol E C K) /\ ((euclidean__axioms.nCol H C K) /\ (euclidean__axioms.nCol E H K)))) as H89.
----------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC E H C K H86).
----------------------------------------------------------------------- destruct H89 as [H90 H91].
destruct H91 as [H92 H93].
destruct H93 as [H94 H95].
exact H95.
---------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K H G) as H90.
----------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry G H K H2).
----------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS K E H G) as H91.
------------------------------------------------------------------------ exists H.
split.
------------------------------------------------------------------------- exact H90.
------------------------------------------------------------------------- split.
-------------------------------------------------------------------------- exact H64.
-------------------------------------------------------------------------- exact H89.
------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS C E H G) as H92.
------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation E H C K G H88 H91).
------------------------------------------------------------------------- assert (exists Q, (euclidean__axioms.BetS C Q G) /\ ((euclidean__axioms.Col E H Q) /\ (euclidean__axioms.nCol E H C))) as H93 by exact H92.
destruct H93 as [Q H94].
destruct H94 as [H95 H96].
destruct H96 as [H97 H98].
assert (* Cut *) (euclidean__defs.Par E f C d) as H99.
-------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C d E f H62).
-------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.TP E f C d) as H100.
--------------------------------------------------------------------------- apply (@lemma__paralleldef2B.lemma__paralleldef2B E f C d H99).
--------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS C d E f) as H101.
---------------------------------------------------------------------------- destruct H100 as [H101 H102].
destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
destruct H87 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H106.
---------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS d C E f) as H102.
----------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.OS d C E f) /\ ((euclidean__defs.OS C d f E) /\ (euclidean__defs.OS d C f E))) as H102.
------------------------------------------------------------------------------ apply (@lemma__samesidesymmetric.lemma__samesidesymmetric E f C d H101).
------------------------------------------------------------------------------ destruct H102 as [H103 H104].
destruct H104 as [H105 H106].
exact H103.
----------------------------------------------------------------------------- assert (euclidean__axioms.Col E H f) as H103 by exact H36.
assert (* Cut *) (euclidean__axioms.Col H E f) as H104.
------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col H E f) /\ ((euclidean__axioms.Col H f E) /\ ((euclidean__axioms.Col f E H) /\ ((euclidean__axioms.Col E f H) /\ (euclidean__axioms.Col f H E))))) as H104.
------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E H f H103).
------------------------------------------------------------------------------- destruct H104 as [H105 H106].
destruct H106 as [H107 H108].
destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
exact H105.
------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H E Q) as H105.
------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H E Q) /\ ((euclidean__axioms.Col H Q E) /\ ((euclidean__axioms.Col Q E H) /\ ((euclidean__axioms.Col E Q H) /\ (euclidean__axioms.Col Q H E))))) as H105.
-------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E H Q H97).
-------------------------------------------------------------------------------- destruct H105 as [H106 H107].
destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H106.
------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E f Q) as H106.
-------------------------------------------------------------------------------- apply (@euclidean__tactics.not__nCol__Col E f Q).
---------------------------------------------------------------------------------intro H106.
apply (@euclidean__tactics.Col__nCol__False E f Q H106).
----------------------------------------------------------------------------------apply (@lemma__collinear4.lemma__collinear4 H E f Q H104 H105 H39).


-------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C E f) as H107.
--------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C d E) /\ ((euclidean__axioms.nCol C E f) /\ ((euclidean__axioms.nCol d E f) /\ (euclidean__axioms.nCol C d f)))) as H107.
---------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC C d E f H62).
---------------------------------------------------------------------------------- destruct H107 as [H108 H109].
destruct H109 as [H110 H111].
destruct H111 as [H112 H113].
exact H110.
--------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol E f C) as H108.
---------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol E C f) /\ ((euclidean__axioms.nCol E f C) /\ ((euclidean__axioms.nCol f C E) /\ ((euclidean__axioms.nCol C f E) /\ (euclidean__axioms.nCol f E C))))) as H108.
----------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C E f H107).
----------------------------------------------------------------------------------- destruct H108 as [H109 H110].
destruct H110 as [H111 H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
exact H111.
---------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C E f G) as H109.
----------------------------------------------------------------------------------- exists Q.
split.
------------------------------------------------------------------------------------ exact H95.
------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------- exact H106.
------------------------------------------------------------------------------------- exact H108.
----------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS d E f G) as H110.
------------------------------------------------------------------------------------ apply (@lemma__planeseparation.lemma__planeseparation E f d C G H102 H109).
------------------------------------------------------------------------------------ assert (exists P, (euclidean__axioms.BetS d P G) /\ ((euclidean__axioms.Col E f P) /\ (euclidean__axioms.nCol E f d))) as H111 by exact H110.
destruct H111 as [P H112].
destruct H112 as [H113 H114].
destruct H114 as [H115 H116].
assert (* Cut *) (~(~((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)))) as H117.
------------------------------------------------------------------------------------- intro H117.
assert (* Cut *) (euclidean__defs.CR A E G H) as H118.
-------------------------------------------------------------------------------------- apply (@lemma__30helper.lemma__30helper A b E f G H H46 H11 H15).
---------------------------------------------------------------------------------------intro H118.
apply (@H117).
----------------------------------------------------------------------------------------left.
exact H118.


-------------------------------------------------------------------------------------- apply (@H117).
---------------------------------------------------------------------------------------right.
exact H118.

------------------------------------------------------------------------------------- assert (* Cut *) (~(~((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)))) as H118.
-------------------------------------------------------------------------------------- intro H118.
assert (* Cut *) (euclidean__defs.CR C E K H) as H119.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H119.
---------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------- apply (@lemma__30helper.lemma__30helper C d E f K H H62 H19 H15).
-----------------------------------------------------------------------------------------intro H120.
apply (@H118).
------------------------------------------------------------------------------------------left.
exact H120.


--------------------------------------------------------------------------------------- apply (@H117).
----------------------------------------------------------------------------------------intro H120.
apply (@H118).
-----------------------------------------------------------------------------------------right.
exact H119.


-------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col F E H) as H119.
--------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col E H F) /\ ((euclidean__axioms.Col E F H) /\ ((euclidean__axioms.Col F H E) /\ ((euclidean__axioms.Col H F E) /\ (euclidean__axioms.Col F E H))))) as H119.
---------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder H E F H38).
---------------------------------------------------------------------------------------- destruct H119 as [H120 H121].
destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H127.
--------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col B A G) as H120.
---------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col A G B) /\ ((euclidean__axioms.Col A B G) /\ ((euclidean__axioms.Col B G A) /\ ((euclidean__axioms.Col G B A) /\ (euclidean__axioms.Col B A G))))) as H120.
----------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder G A B H25).
----------------------------------------------------------------------------------------- destruct H120 as [H121 H122].
destruct H122 as [H123 H124].
destruct H124 as [H125 H126].
destruct H126 as [H127 H128].
exact H128.
---------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B F E) as H121.
----------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B A E F) /\ ((euclidean__defs.Par A B F E) /\ (euclidean__defs.Par B A F E))) as H121.
------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip A B E F H0).
------------------------------------------------------------------------------------------ destruct H121 as [H122 H123].
destruct H123 as [H124 H125].
exact H124.
----------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B H E) as H122.
------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H122.
------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H123.
-------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
-------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel A B H F E H121 H119 H39).
------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A B E H) as H123.
------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par B A H E) /\ ((euclidean__defs.Par A B E H) /\ (euclidean__defs.Par B A E H))) as H123.
-------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A B H E H122).
-------------------------------------------------------------------------------------------- destruct H123 as [H124 H125].
destruct H125 as [H126 H127].
exact H126.
------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H A B) as H124.
-------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H124.
--------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H125.
---------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A B E H H123).
-------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H B A) as H125.
--------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H E A B) /\ ((euclidean__defs.Par E H B A) /\ (euclidean__defs.Par H E B A))) as H125.
---------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip E H A B H124).
---------------------------------------------------------------------------------------------- destruct H125 as [H126 H127].
destruct H127 as [H128 H129].
exact H128.
--------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H G A) as H126.
---------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H126.
----------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H127.
------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------ exact H73.
---------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H A G) as H127.
----------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H E G A) /\ ((euclidean__defs.Par E H A G) /\ (euclidean__defs.Par H E A G))) as H127.
------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip E H G A H126).
------------------------------------------------------------------------------------------------ destruct H127 as [H128 H129].
destruct H129 as [H130 H131].
exact H130.
----------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A G E H) as H128.
------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H128.
------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H129.
-------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
-------------------------------------------------------------------------------------------------- exact H75.
------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A G H) as H129.
------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A G E) /\ ((euclidean__axioms.nCol A E H) /\ ((euclidean__axioms.nCol G E H) /\ (euclidean__axioms.nCol A G H)))) as H129.
-------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A G E H H128).
-------------------------------------------------------------------------------------------------- destruct H129 as [H130 H131].
destruct H131 as [H132 H133].
destruct H133 as [H134 H135].
exact H135.
------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D F E) as H130.
-------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D C E F) /\ ((euclidean__defs.Par C D F E) /\ (euclidean__defs.Par D C F E))) as H130.
--------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C D E F H1).
--------------------------------------------------------------------------------------------------- destruct H130 as [H131 H132].
destruct H132 as [H133 H134].
exact H133.
-------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D H E) as H131.
--------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H131.
---------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H132.
----------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel C D H F E H130 H119 H39).
--------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D E H) as H132.
---------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D C H E) /\ ((euclidean__defs.Par C D E H) /\ (euclidean__defs.Par D C E H))) as H132.
----------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C D H E H131).
----------------------------------------------------------------------------------------------------- destruct H132 as [H133 H134].
destruct H134 as [H135 H136].
exact H135.
---------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H C D) as H133.
----------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H133.
------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H134.
------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C D E H H132).
----------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H D C) as H134.
------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par H E C D) /\ ((euclidean__defs.Par E H D C) /\ (euclidean__defs.Par H E D C))) as H134.
------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip E H C D H133).
------------------------------------------------------------------------------------------------------- destruct H134 as [H135 H136].
destruct H136 as [H137 H138].
exact H137.
------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col D C K) as H135.
------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col C K D) /\ ((euclidean__axioms.Col C D K) /\ ((euclidean__axioms.Col D K C) /\ ((euclidean__axioms.Col K D C) /\ (euclidean__axioms.Col D C K))))) as H135.
-------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K C D H49).
-------------------------------------------------------------------------------------------------------- destruct H135 as [H136 H137].
destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
exact H143.
------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H K C) as H136.
-------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H136.
--------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H137.
---------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel E H K D C H134 H135 H84).
-------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par E H C K) as H137.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par H E K C) /\ ((euclidean__defs.Par E H C K) /\ (euclidean__defs.Par H E C K))) as H137.
---------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip E H K C H136).
---------------------------------------------------------------------------------------------------------- destruct H137 as [H138 H139].
destruct H139 as [H140 H141].
exact H140.
--------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C K E H) as H138.
---------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H138.
----------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H139.
------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric E H C K H137).
---------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C K H) as H139.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C K E) /\ ((euclidean__axioms.nCol C E H) /\ ((euclidean__axioms.nCol K E H) /\ (euclidean__axioms.nCol C K H)))) as H139.
------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelNC.lemma__parallelNC C K E H H138).
------------------------------------------------------------------------------------------------------------ destruct H139 as [H140 H141].
destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
exact H145.
----------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol K H C) as H140.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol K C H) /\ ((euclidean__axioms.nCol K H C) /\ ((euclidean__axioms.nCol H C K) /\ ((euclidean__axioms.nCol C H K) /\ (euclidean__axioms.nCol H K C))))) as H140.
------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder C K H H139).
------------------------------------------------------------------------------------------------------------- destruct H140 as [H141 H142].
destruct H142 as [H143 H144].
destruct H144 as [H145 H146].
destruct H146 as [H147 H148].
exact H143.
------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol E H K) as H141.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol C K E) /\ ((euclidean__axioms.nCol C E H) /\ ((euclidean__axioms.nCol K E H) /\ (euclidean__axioms.nCol C K H)))) as H141.
-------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC C K E H H138).
-------------------------------------------------------------------------------------------------------------- destruct H141 as [H142 H143].
destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
exact H89.
------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H f) as H142.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H142.
--------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H143.
---------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------- exact H103.
-------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq H f) as H143.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq H f) /\ ((euclidean__axioms.neq E H) /\ (euclidean__axioms.neq E f))) as H143.
---------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E H f H15).
---------------------------------------------------------------------------------------------------------------- destruct H143 as [H144 H145].
destruct H145 as [H146 H147].
exact H144.
--------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq f H) as H144.
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H144.
----------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H145.
------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric H f H143).
---------------------------------------------------------------------------------------------------------------- assert (* Cut *) (H = H) as H145.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H145.
------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H146.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------- exact H63.
----------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H H) as H146.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H146.
------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H147.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
-------------------------------------------------------------------------------------------------------------------- exact H64.
------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol f H K) as H147.
------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H147.
-------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H148.
--------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.nCol__notCol f H K).
----------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col f H K).
-----------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper E H K f H H141 H142 H146 H144).


------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol K H f) as H148.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H f K) /\ ((euclidean__axioms.nCol H K f) /\ ((euclidean__axioms.nCol K f H) /\ ((euclidean__axioms.nCol f K H) /\ (euclidean__axioms.nCol K H f))))) as H148.
--------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder f H K H147).
--------------------------------------------------------------------------------------------------------------------- destruct H148 as [H149 H150].
destruct H150 as [H151 H152].
destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
exact H156.
-------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H H) as H149.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H149.
---------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H150.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H145.
--------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C d) as H150.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H150.
----------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H))).
------------------------------------------------------------------------------------------------------------------------intro H150.
assert (* Cut *) (False) as H151.
------------------------------------------------------------------------------------------------------------------------- apply (@H117 H150).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) -> False) as H152.
-------------------------------------------------------------------------------------------------------------------------- intro H152.
apply (@H150).
---------------------------------------------------------------------------------------------------------------------------left.
exact H152.

-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A E G H) -> False) as H153.
--------------------------------------------------------------------------------------------------------------------------- intro H153.
apply (@H150).
----------------------------------------------------------------------------------------------------------------------------right.
exact H153.

--------------------------------------------------------------------------------------------------------------------------- contradiction H151.

----------------------------------------------------------------------------------------------------------------------- assert ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H151 by exact H150.
assert ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as __TmpHyp by exact H151.
destruct __TmpHyp as [H152|H152].
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.TS A G H f) as H153.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.TS A G H f) /\ ((euclidean__axioms.TS A H G f) /\ ((euclidean__axioms.TS f G H A) /\ (euclidean__axioms.TS f H G A)))) as H153.
-------------------------------------------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite A f G H H152 H129).
-------------------------------------------------------------------------------------------------------------------------- destruct H153 as [H154 H155].
destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
exact H154.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C d) as H154.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H154.
--------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H))).
----------------------------------------------------------------------------------------------------------------------------intro H154.
assert (* Cut *) (False) as H155.
----------------------------------------------------------------------------------------------------------------------------- apply (@H118 H154).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) -> False) as H156.
------------------------------------------------------------------------------------------------------------------------------ intro H156.
apply (@H154).
-------------------------------------------------------------------------------------------------------------------------------left.
exact H156.

------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR C E K H) -> False) as H157.
------------------------------------------------------------------------------------------------------------------------------- intro H157.
apply (@H154).
--------------------------------------------------------------------------------------------------------------------------------right.
exact H157.

------------------------------------------------------------------------------------------------------------------------------- contradiction H155.

--------------------------------------------------------------------------------------------------------------------------- assert ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H155 by exact H154.
assert ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as __TmpHyp0 by exact H155.
destruct __TmpHyp0 as [H156|H156].
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS f H K C) as H157.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.TS C K H f) /\ ((euclidean__axioms.TS C H K f) /\ ((euclidean__axioms.TS f K H C) /\ (euclidean__axioms.TS f H K C)))) as H157.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite C f K H H156 H139).
------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
exact H163.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C d) as H158.
------------------------------------------------------------------------------------------------------------------------------ apply (@proposition__30A.proposition__30A A b C d E f G H K H46 H62 H2 H11 H15 H19 H153 H157).
------------------------------------------------------------------------------------------------------------------------------ exact H158.
---------------------------------------------------------------------------------------------------------------------------- assert (exists M, (euclidean__axioms.BetS C M E) /\ (euclidean__axioms.BetS K M H)) as H157 by exact H156.
destruct H157 as [M H158].
destruct H158 as [H159 H160].
assert (* Cut *) (euclidean__axioms.Col K M H) as H161.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H161.
------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H162.
------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------- right.
right.
right.
right.
left.
exact H160.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H M) as H162.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col M K H) /\ ((euclidean__axioms.Col M H K) /\ ((euclidean__axioms.Col H K M) /\ ((euclidean__axioms.Col K H M) /\ (euclidean__axioms.Col H M K))))) as H162.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K M H H161).
------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
exact H169.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS f H E) as H163.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H163.
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H164.
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E H f H15).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS f C K H) as H164.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H164.
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H165.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------- exists E.
exists H.
exists M.
split.
----------------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H162.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H163.
------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H159.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H148.
--------------------------------------------------------------------------------------------------------------------------------------- exact H140.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (K = K) as H165.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H165.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H166.
----------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point K).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H K) as H166.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H166.
----------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H167.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------ right.
left.
exact H165.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C K H d) as H167.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H167.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H168.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------- exists K.
split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H166.
--------------------------------------------------------------------------------------------------------------------------------------- exact H140.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS f K H d) as H168.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H168.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H169.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation K H f C d H164 H167).
------------------------------------------------------------------------------------------------------------------------------------ assert (exists m, (euclidean__axioms.BetS f m d) /\ ((euclidean__axioms.Col K H m) /\ (euclidean__axioms.nCol K H f))) as H169 by exact H168.
destruct H169 as [m H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
assert (* Cut *) (euclidean__defs.Par f E C d) as H175.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H175.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H176.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C d f E H76).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet f E C d)) as H176.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__30.parnotmeet f E C d H175).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col f H E) as H177.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H E f) /\ ((euclidean__axioms.Col H f E) /\ ((euclidean__axioms.Col f E H) /\ ((euclidean__axioms.Col E f H) /\ (euclidean__axioms.Col f H E))))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder E H f H142).
---------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
exact H185.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq f E) as H178.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m d) /\ ((euclidean__axioms.neq f m) /\ (euclidean__axioms.neq f d))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal f m d H171).
----------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
exact H43.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq f H) as H179.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H179.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H180.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------- exact H144.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K d) as H180.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq K d) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C d))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C K d H19).
------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
exact H181.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H K m) as H181.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H K m) /\ ((euclidean__axioms.Col H m K) /\ ((euclidean__axioms.Col m K H) /\ ((euclidean__axioms.Col K m H) /\ (euclidean__axioms.Col m H K))))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K H m H173).
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
exact H182.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H m K) as H182.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H182.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H183.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween f E C d H K m H177 H81 H178 H55 H179 H180 H176 H171 H181).
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K m H) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H183.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H184.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry H m K H182).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS d m f) as H184.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H184.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry f m d H171).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR d f K H) as H185.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------- exists m.
split.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C K H) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol H K f) /\ ((euclidean__axioms.nCol H f K) /\ ((euclidean__axioms.nCol f K H) /\ ((euclidean__axioms.nCol K f H) /\ (euclidean__axioms.nCol f H K))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder K H f H174).
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
exact H139.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C K d) as H187.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H187.
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq d K) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K d H180).
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C K K) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H165.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d K H) as H190.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol d K H).
-------------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col d K H).
--------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper C K H d K H186 H187 H189 H188).


---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS d H K f) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.TS d K H f) /\ ((euclidean__axioms.TS d H K f) /\ ((euclidean__axioms.TS f K H d) /\ (euclidean__axioms.TS f H K d)))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite d f K H H185 H190).
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
exact H194.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par d C E f) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par d C f E) /\ ((euclidean__defs.Par C d E f) /\ (euclidean__defs.Par d C E f))) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C d f E H76).
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
exact H196.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS d K C) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H193.
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C K d H19).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS f H K d) as H194.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H195.
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric H K d f H191).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b d C) as H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__30A.proposition__30A A b d C E f G H K H46 H192 H2 H11 H15 H193 H153 H194).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C d) as H196.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par b A d C) /\ ((euclidean__defs.Par A b C d) /\ (euclidean__defs.Par b A C d))) as H196.
----------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A b d C H195).
----------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H196 as [H197 H198].
destruct H198 as [H199 H200].
exact H199.
---------------------------------------------------------------------------------------------------------------------------------------------------------- exact H196.
-------------------------------------------------------------------------------------------------------------------------- exact H154.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__defs.Par A b C d) as H153.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H153.
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H))).
---------------------------------------------------------------------------------------------------------------------------intro H153.
assert (* Cut *) (False) as H154.
---------------------------------------------------------------------------------------------------------------------------- apply (@H118 H153).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) -> False) as H155.
----------------------------------------------------------------------------------------------------------------------------- intro H155.
apply (@H153).
------------------------------------------------------------------------------------------------------------------------------left.
exact H155.

----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C E K H) -> False) as H156.
------------------------------------------------------------------------------------------------------------------------------ intro H156.
apply (@H153).
-------------------------------------------------------------------------------------------------------------------------------right.
exact H156.

------------------------------------------------------------------------------------------------------------------------------ contradiction H154.

-------------------------------------------------------------------------------------------------------------------------- assert ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H154 by exact H153.
assert ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as __TmpHyp0 by exact H154.
destruct __TmpHyp0 as [H155|H155].
--------------------------------------------------------------------------------------------------------------------------- assert (exists M, (euclidean__axioms.BetS C M f) /\ (euclidean__axioms.BetS K M H)) as H156 by exact H155.
destruct H156 as [M H157].
destruct H157 as [H158 H159].
assert (* Cut *) (euclidean__axioms.Col K M H) as H160.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H160.
----------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H161.
------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------ right.
right.
right.
right.
left.
exact H159.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H M) as H161.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col M K H) /\ ((euclidean__axioms.Col M H K) /\ ((euclidean__axioms.Col H K M) /\ ((euclidean__axioms.Col K H M) /\ (euclidean__axioms.Col H M K))))) as H161.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder K M H H160).
------------------------------------------------------------------------------------------------------------------------------ destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
exact H168.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol K H E) as H162.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol H E K) /\ ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol K E H) /\ ((euclidean__axioms.nCol E K H) /\ (euclidean__axioms.nCol K H E))))) as H162.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder E H K H141).
------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
exact H170.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol K H C) as H163.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol H E K) /\ ((euclidean__axioms.nCol E K H) /\ ((euclidean__axioms.nCol K E H) /\ (euclidean__axioms.nCol E H K))))) as H163.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder K H E H162).
-------------------------------------------------------------------------------------------------------------------------------- destruct H163 as [H164 H165].
destruct H165 as [H166 H167].
destruct H167 as [H168 H169].
destruct H169 as [H170 H171].
exact H140.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.OS E C K H) as H164.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H164.
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H165.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------- exists f.
exists H.
exists M.
split.
----------------------------------------------------------------------------------------------------------------------------------- exact H149.
----------------------------------------------------------------------------------------------------------------------------------- split.
------------------------------------------------------------------------------------------------------------------------------------ exact H161.
------------------------------------------------------------------------------------------------------------------------------------ split.
------------------------------------------------------------------------------------------------------------------------------------- exact H15.
------------------------------------------------------------------------------------------------------------------------------------- split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H158.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H162.
--------------------------------------------------------------------------------------------------------------------------------------- exact H163.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (K = K) as H165.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H165.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H166.
----------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------- apply (@logic.eq__refl Point K).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col K H K) as H166.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H166.
----------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H167.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------ right.
left.
exact H165.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C K H d) as H167.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H167.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H168.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------- exists K.
split.
-------------------------------------------------------------------------------------------------------------------------------------- exact H19.
-------------------------------------------------------------------------------------------------------------------------------------- split.
--------------------------------------------------------------------------------------------------------------------------------------- exact H166.
--------------------------------------------------------------------------------------------------------------------------------------- exact H163.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E K H d) as H168.
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H168.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H169.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
-------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__planeseparation.lemma__planeseparation K H E C d H164 H167).
------------------------------------------------------------------------------------------------------------------------------------ assert (exists m, (euclidean__axioms.BetS E m d) /\ ((euclidean__axioms.Col K H m) /\ (euclidean__axioms.nCol K H E))) as H169 by exact H168.
destruct H169 as [m H170].
destruct H170 as [H171 H172].
destruct H172 as [H173 H174].
assert (* Cut *) (euclidean__defs.Par E f C d) as H175.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H175.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H176.
--------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------------- exact H99.
------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (~(euclidean__defs.Meet E f C d)) as H176.
-------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__30.parnotmeet E f C d H175).
-------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col E H f) as H177.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H K m) /\ ((euclidean__axioms.Col H m K) /\ ((euclidean__axioms.Col m K H) /\ ((euclidean__axioms.Col K m H) /\ (euclidean__axioms.Col m H K))))) as H177.
---------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K H m H173).
---------------------------------------------------------------------------------------------------------------------------------------- destruct H177 as [H178 H179].
destruct H179 as [H180 H181].
destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
exact H142.
--------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E f) as H178.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq m d) /\ ((euclidean__axioms.neq E m) /\ (euclidean__axioms.neq E d))) as H178.
----------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal E m d H171).
----------------------------------------------------------------------------------------------------------------------------------------- destruct H178 as [H179 H180].
destruct H180 as [H181 H182].
exact H42.
---------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq E H) as H179.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H179.
------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H180.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------- exact H7.
----------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq K d) as H180.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.neq K d) /\ ((euclidean__axioms.neq C K) /\ (euclidean__axioms.neq C d))) as H180.
------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal C K d H19).
------------------------------------------------------------------------------------------------------------------------------------------- destruct H180 as [H181 H182].
destruct H182 as [H183 H184].
exact H181.
------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col H K m) as H181.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.Col H K m) /\ ((euclidean__axioms.Col H m K) /\ ((euclidean__axioms.Col m K H) /\ ((euclidean__axioms.Col K m H) /\ (euclidean__axioms.Col m H K))))) as H181.
-------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder K H m H173).
-------------------------------------------------------------------------------------------------------------------------------------------- destruct H181 as [H182 H183].
destruct H183 as [H184 H185].
destruct H185 as [H186 H187].
destruct H187 as [H188 H189].
exact H182.
------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS H m K) as H182.
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H182.
--------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H183.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearbetween.lemma__collinearbetween E f C d H K m H177 H81 H178 H55 H179 H180 H176 H171 H181).
-------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS K m H) as H183.
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H183.
---------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H184.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry H m K H182).
--------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS d m E) as H184.
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H184.
----------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry E m d H171).
---------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.CR d E K H) as H185.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H185.
------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------- exists m.
split.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H184.
-------------------------------------------------------------------------------------------------------------------------------------------------- exact H183.
----------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol C K H) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.nCol H K E) /\ ((euclidean__axioms.nCol H E K) /\ ((euclidean__axioms.nCol E K H) /\ ((euclidean__axioms.nCol K E H) /\ (euclidean__axioms.nCol E H K))))) as H186.
------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCorder.lemma__NCorder K H E H174).
------------------------------------------------------------------------------------------------------------------------------------------------- destruct H186 as [H187 H188].
destruct H188 as [H189 H190].
destruct H190 as [H191 H192].
destruct H192 as [H193 H194].
exact H139.
------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.Col C K d) as H187.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H187.
-------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------------------------- exact H81.
------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq d K) as H188.
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H188.
--------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric K d H180).
-------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col C K K) as H189.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H189.
---------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------------------------- right.
right.
left.
exact H165.
--------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.nCol d K H) as H190.
---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H190.
----------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.nCol__notCol d K H).
-------------------------------------------------------------------------------------------------------------------------------------------------------apply (@euclidean__tactics.nCol__not__Col d K H).
--------------------------------------------------------------------------------------------------------------------------------------------------------apply (@lemma__NChelper.lemma__NChelper C K H d K H186 H187 H189 H188).


---------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS d H K E) as H191.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.TS d K H E) /\ ((euclidean__axioms.TS d H K E) /\ ((euclidean__axioms.TS E K H d) /\ (euclidean__axioms.TS E H K d)))) as H191.
------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite d E K H H185 H190).
------------------------------------------------------------------------------------------------------------------------------------------------------ destruct H191 as [H192 H193].
destruct H193 as [H194 H195].
destruct H195 as [H196 H197].
exact H194.
----------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par d C f E) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par d C f E) /\ ((euclidean__defs.Par C d E f) /\ (euclidean__defs.Par d C E f))) as H192.
------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C d f E H76).
------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H192 as [H193 H194].
destruct H194 as [H195 H196].
exact H193.
------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS d K C) as H193.
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H193.
-------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry C K d H19).
------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E H K d) as H194.
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H194.
--------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H195.
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric H K d E H191).
-------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A G H E) as H195.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.TS A G H E) /\ ((euclidean__axioms.TS A H G E) /\ ((euclidean__axioms.TS E G H A) /\ (euclidean__axioms.TS E H G A)))) as H195.
---------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite A E G H H152 H129).
---------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H195 as [H196 H197].
destruct H197 as [H198 H199].
destruct H199 as [H200 H201].
exact H196.
--------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.BetS f H E) as H196.
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H196.
----------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry E H f H15).
---------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b d C) as H197.
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H197.
------------------------------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__30A.proposition__30A A b d C f E G H K H68 H192 H2 H11 H196 H193 H195 H194).
----------------------------------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C d) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.Par b A d C) /\ ((euclidean__defs.Par A b C d) /\ (euclidean__defs.Par b A C d))) as H198.
------------------------------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A b d C H197).
------------------------------------------------------------------------------------------------------------------------------------------------------------- destruct H198 as [H199 H200].
destruct H200 as [H201 H202].
exact H201.
------------------------------------------------------------------------------------------------------------------------------------------------------------ exact H198.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS C H K E) as H156.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.TS C K H E) /\ ((euclidean__axioms.TS C H K E) /\ ((euclidean__axioms.TS E K H C) /\ (euclidean__axioms.TS E H K C)))) as H156.
----------------------------------------------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite C E K H H155 H139).
----------------------------------------------------------------------------------------------------------------------------- destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
exact H159.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS E H K C) as H157.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H157.
------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H158.
------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__oppositesidesymmetric.lemma__oppositesidesymmetric H K C E H156).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.TS A G H E) as H158.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.TS A G H E) /\ ((euclidean__axioms.TS A H G E) /\ ((euclidean__axioms.TS E G H A) /\ (euclidean__axioms.TS E H G A)))) as H158.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__crossimpliesopposite.lemma__crossimpliesopposite A E G H H152 H129).
------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
exact H159.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.BetS f H E) as H159.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H159.
-------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H160.
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__axioms.axiom__betweennesssymmetry E H f H15).
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C d) as H160.
-------------------------------------------------------------------------------------------------------------------------------- apply (@proposition__30A.proposition__30A A b C d f E G H K H68 H76 H2 H11 H159 H19 H158 H157).
-------------------------------------------------------------------------------------------------------------------------------- exact H160.
------------------------------------------------------------------------------------------------------------------------- exact H153.
---------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b d C) as H151.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par b A C d) /\ ((euclidean__defs.Par A b d C) /\ (euclidean__defs.Par b A d C))) as H151.
------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip A b C d H150).
------------------------------------------------------------------------------------------------------------------------ destruct H151 as [H152 H153].
destruct H153 as [H154 H155].
exact H154.
----------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col d C D) as H152.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col C D d) /\ ((euclidean__axioms.Col C d D) /\ ((euclidean__axioms.Col d D C) /\ ((euclidean__axioms.Col D d C) /\ (euclidean__axioms.Col d C D))))) as H152.
------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder D C d H52).
------------------------------------------------------------------------------------------------------------------------- destruct H152 as [H153 H154].
destruct H154 as [H155 H156].
destruct H156 as [H157 H158].
destruct H158 as [H159 H160].
exact H160.
------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.neq D C) as H153.
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H153.
-------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H154.
--------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
--------------------------------------------------------------------------------------------------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C D H22).
------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b D C) as H154.
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H154.
--------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H155.
---------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel A b D d C H151 H152 H153).
-------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A b C D) as H155.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par b A D C) /\ ((euclidean__defs.Par A b C D) /\ (euclidean__defs.Par b A C D))) as H155.
---------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip A b D C H154).
---------------------------------------------------------------------------------------------------------------------------- destruct H155 as [H156 H157].
destruct H157 as [H158 H159].
exact H158.
--------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D A b) as H156.
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H156.
----------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H157.
------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelsymmetric.lemma__parallelsymmetric A b C D H155).
---------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D b A) as H157.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D C A b) /\ ((euclidean__defs.Par C D b A) /\ (euclidean__defs.Par D C b A))) as H157.
------------------------------------------------------------------------------------------------------------------------------ apply (@lemma__parallelflip.lemma__parallelflip C D A b H156).
------------------------------------------------------------------------------------------------------------------------------ destruct H157 as [H158 H159].
destruct H159 as [H160 H161].
exact H160.
----------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.Col b A B) as H158.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__axioms.Col A B b) /\ ((euclidean__axioms.Col A b B) /\ ((euclidean__axioms.Col b B A) /\ ((euclidean__axioms.Col B b A) /\ (euclidean__axioms.Col b A B))))) as H158.
------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearorder.lemma__collinearorder B A b H28).
------------------------------------------------------------------------------------------------------------------------------- destruct H158 as [H159 H160].
destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
exact H166.
------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) (euclidean__axioms.nCol A B E) as H159.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.nCol A B E) /\ ((euclidean__axioms.nCol A E H) /\ ((euclidean__axioms.nCol B E H) /\ (euclidean__axioms.nCol A B H)))) as H159.
-------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelNC.lemma__parallelNC A B E H H123).
-------------------------------------------------------------------------------------------------------------------------------- destruct H159 as [H160 H161].
destruct H161 as [H162 H163].
destruct H163 as [H164 H165].
exact H160.
------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__axioms.neq B A) as H160.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq A E) /\ ((euclidean__axioms.neq B A) /\ ((euclidean__axioms.neq E B) /\ (euclidean__axioms.neq E A)))))) as H160.
--------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__NCdistinct.lemma__NCdistinct A B E H159).
--------------------------------------------------------------------------------------------------------------------------------- destruct H160 as [H161 H162].
destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
destruct H166 as [H167 H168].
destruct H168 as [H169 H170].
exact H167.
-------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D B A) as H161.
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H161.
---------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H162.
----------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
----------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__collinearparallel.lemma__collinearparallel C D B b A H157 H158 H160).
--------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par C D A B) as H162.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.Par D C B A) /\ ((euclidean__defs.Par C D A B) /\ (euclidean__defs.Par D C A B))) as H162.
----------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelflip.lemma__parallelflip C D B A H161).
----------------------------------------------------------------------------------------------------------------------------------- destruct H162 as [H163 H164].
destruct H164 as [H165 H166].
exact H165.
---------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) (euclidean__defs.Par A B C D) as H163.
----------------------------------------------------------------------------------------------------------------------------------- assert (* Cut *) ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) as H163.
------------------------------------------------------------------------------------------------------------------------------------ apply (@euclidean__tactics.NNPP ((euclidean__defs.CR C f K H) \/ (euclidean__defs.CR C E K H)) H118).
------------------------------------------------------------------------------------------------------------------------------------ assert (* Cut *) ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) as H164.
------------------------------------------------------------------------------------------------------------------------------------- apply (@euclidean__tactics.NNPP ((euclidean__defs.CR A f G H) \/ (euclidean__defs.CR A E G H)) H117).
------------------------------------------------------------------------------------------------------------------------------------- apply (@lemma__parallelsymmetric.lemma__parallelsymmetric C D A B H162).
----------------------------------------------------------------------------------------------------------------------------------- exact H163.
Qed.
