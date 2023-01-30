Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export euclidean__tactics.
Require Export lemma__3__6b.
Require Export lemma__betweennotequal.
Require Export lemma__collinear4.
Require Export lemma__collinearorder.
Require Export lemma__congruenceflip.
Require Export lemma__congruencesymmetric.
Require Export lemma__congruencetransitive.
Require Export lemma__extension.
Require Export lemma__inequalitysymmetric.
Require Export logic.
Require Export proposition__10.
Definition proposition__12 : forall A B C, (euclidean__axioms.nCol A B C) -> (exists X, euclidean__defs.Perp__at C X A B X).
Proof.
intro A.
intro B.
intro C.
intro H.
assert (* Cut *) (~(B = C)) as H0.
- intro H0.
assert (* Cut *) (euclidean__axioms.Col A B C) as H1.
-- right.
right.
left.
exact H0.
-- apply (@euclidean__tactics.Col__nCol__False A B C H H1).
- assert (* Cut *) (euclidean__axioms.neq C B) as H1.
-- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B C H0).
-- assert (* Cut *) (~(A = B)) as H2.
--- intro H2.
assert (* Cut *) (euclidean__axioms.Col A B C) as H3.
---- left.
exact H2.
---- apply (@euclidean__tactics.Col__nCol__False A B C H H3).
--- assert (* Cut *) (exists E, (euclidean__axioms.BetS C B E) /\ (euclidean__axioms.Cong B E C B)) as H3.
---- apply (@lemma__extension.lemma__extension C B C B H1 H1).
---- destruct H3 as [E H4].
destruct H4 as [H5 H6].
assert (* Cut *) (euclidean__axioms.neq C E) as H7.
----- assert (* Cut *) ((euclidean__axioms.neq B E) /\ ((euclidean__axioms.neq C B) /\ (euclidean__axioms.neq C E))) as H7.
------ apply (@lemma__betweennotequal.lemma__betweennotequal C B E H5).
------ destruct H7 as [H8 H9].
destruct H9 as [H10 H11].
exact H11.
----- assert (* Cut *) (euclidean__axioms.neq E C) as H8.
------ apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric C E H7).
------ assert (* Cut *) (exists F, (euclidean__axioms.BetS E C F) /\ (euclidean__axioms.Cong C F E C)) as H9.
------- apply (@lemma__extension.lemma__extension E C E C H8 H8).
------- destruct H9 as [F H10].
destruct H10 as [H11 H12].
assert (* Cut *) (euclidean__axioms.Cong E C C E) as H13.
-------- apply (@euclidean__axioms.cn__equalityreverse E C).
-------- assert (* Cut *) (euclidean__axioms.Cong C E C E) as H14.
--------- apply (@euclidean__axioms.cn__congruencereflexive C E).
--------- assert (* Cut *) (euclidean__axioms.Cong C F C E) as H15.
---------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C F E C C E H12 H13).
---------- assert (* Cut *) (euclidean__axioms.BetS E B C) as H16.
----------- apply (@euclidean__axioms.axiom__betweennesssymmetry C B E H5).
----------- assert (* Cut *) (euclidean__axioms.BetS E B F) as H17.
------------ apply (@lemma__3__6b.lemma__3__6b E B C F H16 H11).
------------ assert (* Cut *) (exists K, euclidean__axioms.CI K C C E) as H18.
------------- apply (@euclidean__axioms.postulate__Euclid3 C E H7).
------------- destruct H18 as [K H19].
assert (euclidean__axioms.Cong C E C E) as H20 by exact H14.
assert (* Cut *) (euclidean__axioms.Cong C B C B) as H21.
-------------- apply (@euclidean__axioms.cn__congruencereflexive C B).
-------------- assert (* Cut *) (euclidean__axioms.InCirc B K) as H22.
--------------- exists E.
exists B.
exists C.
exists C.
exists E.
split.
---------------- exact H19.
---------------- right.
split.
----------------- exact H5.
----------------- split.
------------------ exact H20.
------------------ exact H21.
--------------- assert (* Cut *) (exists P Q, (euclidean__axioms.Col A B P) /\ ((euclidean__axioms.BetS A B Q) /\ ((euclidean__axioms.OnCirc P K) /\ ((euclidean__axioms.OnCirc Q K) /\ (euclidean__axioms.BetS P B Q))))) as H23.
---------------- apply (@euclidean__axioms.postulate__line__circle A B C K C E H19 H22 H2).
---------------- destruct H23 as [P H24].
destruct H24 as [Q H25].
destruct H25 as [H26 H27].
destruct H27 as [H28 H29].
destruct H29 as [H30 H31].
destruct H31 as [H32 H33].
assert (* Cut *) (euclidean__axioms.Col A B Q) as H34.
----------------- right.
right.
right.
right.
left.
exact H28.
----------------- assert (* Cut *) (euclidean__axioms.Cong C P C E) as H35.
------------------ apply (@euclidean__axioms.axiom__circle__center__radius C C E K P H19 H30).
------------------ assert (* Cut *) (euclidean__axioms.Cong C Q C E) as H36.
------------------- apply (@euclidean__axioms.axiom__circle__center__radius C C E K Q H19 H32).
------------------- assert (* Cut *) (euclidean__axioms.Cong C E C Q) as H37.
-------------------- apply (@lemma__congruencesymmetric.lemma__congruencesymmetric C C Q E H36).
-------------------- assert (* Cut *) (euclidean__axioms.Cong C P C Q) as H38.
--------------------- apply (@lemma__congruencetransitive.lemma__congruencetransitive C P C E C Q H35 H37).
--------------------- assert (* Cut *) (euclidean__axioms.Cong P C Q C) as H39.
---------------------- assert (* Cut *) ((euclidean__axioms.Cong P C Q C) /\ ((euclidean__axioms.Cong P C C Q) /\ (euclidean__axioms.Cong C P Q C))) as H39.
----------------------- apply (@lemma__congruenceflip.lemma__congruenceflip C P C Q H38).
----------------------- destruct H39 as [H40 H41].
destruct H41 as [H42 H43].
exact H40.
---------------------- assert (* Cut *) (euclidean__axioms.neq P Q) as H40.
----------------------- assert (* Cut *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q))) as H40.
------------------------ apply (@lemma__betweennotequal.lemma__betweennotequal P B Q H33).
------------------------ destruct H40 as [H41 H42].
destruct H42 as [H43 H44].
exact H44.
----------------------- assert (* Cut *) (exists M, (euclidean__axioms.BetS P M Q) /\ (euclidean__axioms.Cong M P M Q)) as H41.
------------------------ apply (@proposition__10.proposition__10 P Q H40).
------------------------ destruct H41 as [M H42].
destruct H42 as [H43 H44].
assert (* Cut *) (euclidean__axioms.Cong P M Q M) as H45.
------------------------- assert (* Cut *) ((euclidean__axioms.Cong P M Q M) /\ ((euclidean__axioms.Cong P M M Q) /\ (euclidean__axioms.Cong M P Q M))) as H45.
-------------------------- apply (@lemma__congruenceflip.lemma__congruenceflip M P M Q H44).
-------------------------- destruct H45 as [H46 H47].
destruct H47 as [H48 H49].
exact H46.
------------------------- assert (* Cut *) (euclidean__axioms.Col P M Q) as H46.
-------------------------- right.
right.
right.
right.
left.
exact H43.
-------------------------- assert (* Cut *) (euclidean__axioms.Col P B Q) as H47.
--------------------------- right.
right.
right.
right.
left.
exact H33.
--------------------------- assert (* Cut *) (euclidean__axioms.Col P Q B) as H48.
---------------------------- assert (* Cut *) ((euclidean__axioms.Col B P Q) /\ ((euclidean__axioms.Col B Q P) /\ ((euclidean__axioms.Col Q P B) /\ ((euclidean__axioms.Col P Q B) /\ (euclidean__axioms.Col Q B P))))) as H48.
----------------------------- apply (@lemma__collinearorder.lemma__collinearorder P B Q H47).
----------------------------- destruct H48 as [H49 H50].
destruct H50 as [H51 H52].
destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H55.
---------------------------- assert (* Cut *) (euclidean__axioms.Col P Q M) as H49.
----------------------------- assert (* Cut *) ((euclidean__axioms.Col M P Q) /\ ((euclidean__axioms.Col M Q P) /\ ((euclidean__axioms.Col Q P M) /\ ((euclidean__axioms.Col P Q M) /\ (euclidean__axioms.Col Q M P))))) as H49.
------------------------------ apply (@lemma__collinearorder.lemma__collinearorder P M Q H46).
------------------------------ destruct H49 as [H50 H51].
destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
exact H56.
----------------------------- assert (* Cut *) (euclidean__axioms.Col Q B M) as H50.
------------------------------ apply (@euclidean__tactics.not__nCol__Col Q B M).
-------------------------------intro H50.
apply (@euclidean__tactics.Col__nCol__False Q B M H50).
--------------------------------apply (@lemma__collinear4.lemma__collinear4 P Q B M H48 H49 H40).


------------------------------ assert (* Cut *) (euclidean__axioms.Col Q B A) as H51.
------------------------------- assert (* Cut *) ((euclidean__axioms.Col B A Q) /\ ((euclidean__axioms.Col B Q A) /\ ((euclidean__axioms.Col Q A B) /\ ((euclidean__axioms.Col A Q B) /\ (euclidean__axioms.Col Q B A))))) as H51.
-------------------------------- apply (@lemma__collinearorder.lemma__collinearorder A B Q H34).
-------------------------------- destruct H51 as [H52 H53].
destruct H53 as [H54 H55].
destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
exact H59.
------------------------------- assert (* Cut *) (euclidean__axioms.neq B Q) as H52.
-------------------------------- assert (* Cut *) ((euclidean__axioms.neq B Q) /\ ((euclidean__axioms.neq P B) /\ (euclidean__axioms.neq P Q))) as H52.
--------------------------------- apply (@lemma__betweennotequal.lemma__betweennotequal P B Q H33).
--------------------------------- destruct H52 as [H53 H54].
destruct H54 as [H55 H56].
exact H53.
-------------------------------- assert (* Cut *) (euclidean__axioms.neq Q B) as H53.
--------------------------------- apply (@lemma__inequalitysymmetric.lemma__inequalitysymmetric B Q H52).
--------------------------------- assert (* Cut *) (euclidean__axioms.Col B M A) as H54.
---------------------------------- apply (@euclidean__tactics.not__nCol__Col B M A).
-----------------------------------intro H54.
apply (@euclidean__tactics.Col__nCol__False B M A H54).
------------------------------------apply (@lemma__collinear4.lemma__collinear4 Q B M A H50 H51 H53).


---------------------------------- assert (* Cut *) (euclidean__axioms.Col A B M) as H55.
----------------------------------- assert (* Cut *) ((euclidean__axioms.Col M B A) /\ ((euclidean__axioms.Col M A B) /\ ((euclidean__axioms.Col A B M) /\ ((euclidean__axioms.Col B A M) /\ (euclidean__axioms.Col A M B))))) as H55.
------------------------------------ apply (@lemma__collinearorder.lemma__collinearorder B M A H54).
------------------------------------ destruct H55 as [H56 H57].
destruct H57 as [H58 H59].
destruct H59 as [H60 H61].
destruct H61 as [H62 H63].
exact H60.
----------------------------------- assert (* Cut *) (~(M = C)) as H56.
------------------------------------ intro H56.
assert (* Cut *) (euclidean__axioms.Col A B C) as H57.
------------------------------------- apply (@eq__ind__r euclidean__axioms.Point C (fun M0 => (euclidean__axioms.BetS P M0 Q) -> ((euclidean__axioms.Cong M0 P M0 Q) -> ((euclidean__axioms.Cong P M0 Q M0) -> ((euclidean__axioms.Col P M0 Q) -> ((euclidean__axioms.Col P Q M0) -> ((euclidean__axioms.Col Q B M0) -> ((euclidean__axioms.Col B M0 A) -> ((euclidean__axioms.Col A B M0) -> (euclidean__axioms.Col A B C)))))))))) with (x := M).
--------------------------------------intro H57.
intro H58.
intro H59.
intro H60.
intro H61.
intro H62.
intro H63.
intro H64.
exact H64.

-------------------------------------- exact H56.
-------------------------------------- exact H43.
-------------------------------------- exact H44.
-------------------------------------- exact H45.
-------------------------------------- exact H46.
-------------------------------------- exact H49.
-------------------------------------- exact H50.
-------------------------------------- exact H54.
-------------------------------------- exact H55.
------------------------------------- apply (@euclidean__tactics.Col__nCol__False A B C H H57).
------------------------------------ assert (* Cut *) (euclidean__defs.Per P M C) as H57.
------------------------------------- exists Q.
split.
-------------------------------------- exact H43.
-------------------------------------- split.
--------------------------------------- exact H45.
--------------------------------------- split.
---------------------------------------- exact H39.
---------------------------------------- exact H56.
------------------------------------- assert (* Cut *) (M = M) as H58.
-------------------------------------- apply (@logic.eq__refl Point M).
-------------------------------------- assert (* Cut *) (euclidean__axioms.Col C M M) as H59.
--------------------------------------- right.
right.
left.
exact H58.
--------------------------------------- assert (* Cut *) (euclidean__defs.Perp__at C M A B M) as H60.
---------------------------------------- exists P.
split.
----------------------------------------- exact H59.
----------------------------------------- split.
------------------------------------------ exact H55.
------------------------------------------ split.
------------------------------------------- exact H26.
------------------------------------------- exact H57.
---------------------------------------- exists M.
exact H60.
Qed.
