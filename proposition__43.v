Require Export euclidean__axioms.
Require Export euclidean__defs.
Require Export lemma__PGflip.
Require Export logic.
Require Export proposition__34.
Definition proposition__43 : forall (A: euclidean__axioms.Point) (B: euclidean__axioms.Point) (C: euclidean__axioms.Point) (D: euclidean__axioms.Point) (E: euclidean__axioms.Point) (F: euclidean__axioms.Point) (G: euclidean__axioms.Point) (H: euclidean__axioms.Point) (K: euclidean__axioms.Point), (euclidean__defs.PG A B C D) -> ((euclidean__axioms.BetS A H D) -> ((euclidean__axioms.BetS A E B) -> ((euclidean__axioms.BetS D F C) -> ((euclidean__axioms.BetS B G C) -> ((euclidean__axioms.BetS A K C) -> ((euclidean__defs.PG E A H K) -> ((euclidean__defs.PG G K F C) -> (euclidean__axioms.EF K G B E D F K H)))))))).
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
assert (* Cut *) (euclidean__defs.PG B A D C) as H8.
- apply (@lemma__PGflip.lemma__PGflip (A) (B) (C) (D) H0).
- assert (* Cut *) (euclidean__axioms.Cong__3 A B C C D A) as H9.
-- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H9.
--- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
---- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
---- destruct __0 as [__0 __1].
exact __1.
--- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H10.
---- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
----- apply (@H9 (A0) (B0) (C0) (D0) __).
----- destruct __0 as [__0 __1].
exact __1.
---- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H11.
----- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
------ apply (@H10 (A0) (B0) (C0) (D0) __).
------ destruct __0 as [__0 __1].
exact __1.
----- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H12.
------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
------- apply (@H11 (A0) (B0) (C0) (D0) __).
------- destruct __0 as [__0 __1].
exact __1.
------ apply (@H12 (B) (C) (A) (D) H8).
-- assert (* Cut *) (euclidean__axioms.ET A B C C D A) as H10.
--- apply (@euclidean__axioms.axiom__congruentequal (A) (B) (C) (C) (D) (A) H9).
--- assert (* Cut *) (euclidean__axioms.Cong__3 A E K K H A) as H11.
---- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H11.
----- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
------ apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
------ destruct __0 as [__0 __1].
exact __1.
----- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H12.
------ intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
------- apply (@H11 (A0) (B0) (C0) (D0) __).
------- destruct __0 as [__0 __1].
exact __1.
------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H13.
------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
-------- apply (@H12 (A0) (B0) (C0) (D0) __).
-------- destruct __0 as [__0 __1].
exact __1.
------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H14.
-------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
--------- apply (@H13 (A0) (B0) (C0) (D0) __).
--------- destruct __0 as [__0 __1].
exact __1.
-------- apply (@H14 (E) (K) (A) (H) H6).
---- assert (* Cut *) (euclidean__axioms.ET A E K K H A) as H12.
----- apply (@euclidean__axioms.axiom__congruentequal (A) (E) (K) (K) (H) (A) H11).
----- assert (* Cut *) (euclidean__axioms.Cong__3 K G C C F K) as H13.
------ assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as H13.
------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 B0 C0 D0) /\ ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))))) as __0.
-------- apply (@proposition__34.proposition__34 (A0) (B0) (C0) (D0) __).
-------- destruct __0 as [__0 __1].
exact __1.
------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as H14.
-------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__axioms.Cong A0 C0 B0 D0) /\ ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)))) as __0.
--------- apply (@H13 (A0) (B0) (C0) (D0) __).
--------- destruct __0 as [__0 __1].
exact __1.
-------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as H15.
--------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA C0 A0 B0 B0 D0 C0) /\ ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0))) as __0.
---------- apply (@H14 (A0) (B0) (C0) (D0) __).
---------- destruct __0 as [__0 __1].
exact __1.
--------- assert (* Cut *) (forall (A0: euclidean__axioms.Point) (B0: euclidean__axioms.Point) (C0: euclidean__axioms.Point) (D0: euclidean__axioms.Point), (euclidean__defs.PG A0 C0 D0 B0) -> (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as H16.
---------- intro A0.
intro B0.
intro C0.
intro D0.
intro __.
assert (* AndElim *) ((euclidean__defs.CongA A0 B0 D0 D0 C0 A0) /\ (euclidean__axioms.Cong__3 C0 A0 B0 B0 D0 C0)) as __0.
----------- apply (@H15 (A0) (B0) (C0) (D0) __).
----------- destruct __0 as [__0 __1].
exact __1.
---------- apply (@H16 (G) (C) (K) (F) H7).
------ assert (* Cut *) (euclidean__axioms.ET K G C C F K) as H14.
------- apply (@euclidean__axioms.axiom__congruentequal (K) (G) (C) (C) (F) (K) H13).
------- assert (* Cut *) (euclidean__axioms.ET K G C K C F) as H15.
-------- assert (* Cut *) ((euclidean__axioms.ET K G C F K C) /\ ((euclidean__axioms.ET K G C C K F) /\ ((euclidean__axioms.ET K G C F C K) /\ ((euclidean__axioms.ET K G C K F C) /\ (euclidean__axioms.ET K G C K C F))))) as H15.
--------- apply (@euclidean__axioms.axiom__ETpermutation (K) (G) (C) (C) (F) (K) H14).
--------- assert (* AndElim *) ((euclidean__axioms.ET K G C F K C) /\ ((euclidean__axioms.ET K G C C K F) /\ ((euclidean__axioms.ET K G C F C K) /\ ((euclidean__axioms.ET K G C K F C) /\ (euclidean__axioms.ET K G C K C F))))) as H16.
---------- exact H15.
---------- destruct H16 as [H16 H17].
assert (* AndElim *) ((euclidean__axioms.ET K G C C K F) /\ ((euclidean__axioms.ET K G C F C K) /\ ((euclidean__axioms.ET K G C K F C) /\ (euclidean__axioms.ET K G C K C F)))) as H18.
----------- exact H17.
----------- destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.ET K G C F C K) /\ ((euclidean__axioms.ET K G C K F C) /\ (euclidean__axioms.ET K G C K C F))) as H20.
------------ exact H19.
------------ destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.ET K G C K F C) /\ (euclidean__axioms.ET K G C K C F)) as H22.
------------- exact H21.
------------- destruct H22 as [H22 H23].
exact H23.
-------- assert (* Cut *) (euclidean__axioms.ET K C F K G C) as H16.
--------- apply (@euclidean__axioms.axiom__ETsymmetric (K) (G) (C) (K) (C) (F) H15).
--------- assert (* Cut *) (euclidean__axioms.ET K C F K C G) as H17.
---------- assert (* Cut *) ((euclidean__axioms.ET K C F G C K) /\ ((euclidean__axioms.ET K C F K C G) /\ ((euclidean__axioms.ET K C F G K C) /\ ((euclidean__axioms.ET K C F C G K) /\ (euclidean__axioms.ET K C F C K G))))) as H17.
----------- apply (@euclidean__axioms.axiom__ETpermutation (K) (C) (F) (K) (G) (C) H16).
----------- assert (* AndElim *) ((euclidean__axioms.ET K C F G C K) /\ ((euclidean__axioms.ET K C F K C G) /\ ((euclidean__axioms.ET K C F G K C) /\ ((euclidean__axioms.ET K C F C G K) /\ (euclidean__axioms.ET K C F C K G))))) as H18.
------------ exact H17.
------------ destruct H18 as [H18 H19].
assert (* AndElim *) ((euclidean__axioms.ET K C F K C G) /\ ((euclidean__axioms.ET K C F G K C) /\ ((euclidean__axioms.ET K C F C G K) /\ (euclidean__axioms.ET K C F C K G)))) as H20.
------------- exact H19.
------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.ET K C F G K C) /\ ((euclidean__axioms.ET K C F C G K) /\ (euclidean__axioms.ET K C F C K G))) as H22.
-------------- exact H21.
-------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.ET K C F C G K) /\ (euclidean__axioms.ET K C F C K G)) as H24.
--------------- exact H23.
--------------- destruct H24 as [H24 H25].
exact H20.
---------- assert (* Cut *) (euclidean__axioms.ET K C G K C F) as H18.
----------- apply (@euclidean__axioms.axiom__ETsymmetric (K) (C) (F) (K) (C) (G) H17).
----------- assert (* Cut *) (euclidean__axioms.ET A B C A C D) as H19.
------------ assert (* Cut *) ((euclidean__axioms.ET A B C D A C) /\ ((euclidean__axioms.ET A B C C A D) /\ ((euclidean__axioms.ET A B C D C A) /\ ((euclidean__axioms.ET A B C A D C) /\ (euclidean__axioms.ET A B C A C D))))) as H19.
------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (B) (C) (C) (D) (A) H10).
------------- assert (* AndElim *) ((euclidean__axioms.ET A B C D A C) /\ ((euclidean__axioms.ET A B C C A D) /\ ((euclidean__axioms.ET A B C D C A) /\ ((euclidean__axioms.ET A B C A D C) /\ (euclidean__axioms.ET A B C A C D))))) as H20.
-------------- exact H19.
-------------- destruct H20 as [H20 H21].
assert (* AndElim *) ((euclidean__axioms.ET A B C C A D) /\ ((euclidean__axioms.ET A B C D C A) /\ ((euclidean__axioms.ET A B C A D C) /\ (euclidean__axioms.ET A B C A C D)))) as H22.
--------------- exact H21.
--------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.ET A B C D C A) /\ ((euclidean__axioms.ET A B C A D C) /\ (euclidean__axioms.ET A B C A C D))) as H24.
---------------- exact H23.
---------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.ET A B C A D C) /\ (euclidean__axioms.ET A B C A C D)) as H26.
----------------- exact H25.
----------------- destruct H26 as [H26 H27].
exact H27.
------------ assert (* Cut *) (euclidean__axioms.ET A C D A B C) as H20.
------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (B) (C) (A) (C) (D) H19).
------------- assert (* Cut *) (euclidean__axioms.ET A C D A C B) as H21.
-------------- assert (* Cut *) ((euclidean__axioms.ET A C D B C A) /\ ((euclidean__axioms.ET A C D A C B) /\ ((euclidean__axioms.ET A C D B A C) /\ ((euclidean__axioms.ET A C D C B A) /\ (euclidean__axioms.ET A C D C A B))))) as H21.
--------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (C) (D) (A) (B) (C) H20).
--------------- assert (* AndElim *) ((euclidean__axioms.ET A C D B C A) /\ ((euclidean__axioms.ET A C D A C B) /\ ((euclidean__axioms.ET A C D B A C) /\ ((euclidean__axioms.ET A C D C B A) /\ (euclidean__axioms.ET A C D C A B))))) as H22.
---------------- exact H21.
---------------- destruct H22 as [H22 H23].
assert (* AndElim *) ((euclidean__axioms.ET A C D A C B) /\ ((euclidean__axioms.ET A C D B A C) /\ ((euclidean__axioms.ET A C D C B A) /\ (euclidean__axioms.ET A C D C A B)))) as H24.
----------------- exact H23.
----------------- destruct H24 as [H24 H25].
assert (* AndElim *) ((euclidean__axioms.ET A C D B A C) /\ ((euclidean__axioms.ET A C D C B A) /\ (euclidean__axioms.ET A C D C A B))) as H26.
------------------ exact H25.
------------------ destruct H26 as [H26 H27].
assert (* AndElim *) ((euclidean__axioms.ET A C D C B A) /\ (euclidean__axioms.ET A C D C A B)) as H28.
------------------- exact H27.
------------------- destruct H28 as [H28 H29].
exact H24.
-------------- assert (* Cut *) (euclidean__axioms.ET A C B A C D) as H22.
--------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (C) (D) (A) (C) (B) H21).
--------------- assert (* Cut *) (euclidean__axioms.EF A K G B A K F D) as H23.
---------------- apply (@euclidean__axioms.axiom__cutoff1 (A) (K) (C) (G) (B) (A) (K) (C) (F) (D) (H5) (H5) (H4) (H3) (H18) H22).
---------------- assert (* Cut *) (euclidean__axioms.BetS B E A) as H24.
----------------- apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (E) (B) H2).
----------------- assert (* Cut *) (euclidean__axioms.BetS D H A) as H25.
------------------ apply (@euclidean__axioms.axiom__betweennesssymmetry (A) (H) (D) H1).
------------------ assert (* Cut *) (euclidean__axioms.ET A E K H A K) as H26.
------------------- assert (* Cut *) ((euclidean__axioms.ET A E K H A K) /\ ((euclidean__axioms.ET A E K K A H) /\ ((euclidean__axioms.ET A E K H K A) /\ ((euclidean__axioms.ET A E K A H K) /\ (euclidean__axioms.ET A E K A K H))))) as H26.
-------------------- apply (@euclidean__axioms.axiom__ETpermutation (A) (E) (K) (K) (H) (A) H12).
-------------------- assert (* AndElim *) ((euclidean__axioms.ET A E K H A K) /\ ((euclidean__axioms.ET A E K K A H) /\ ((euclidean__axioms.ET A E K H K A) /\ ((euclidean__axioms.ET A E K A H K) /\ (euclidean__axioms.ET A E K A K H))))) as H27.
--------------------- exact H26.
--------------------- destruct H27 as [H27 H28].
assert (* AndElim *) ((euclidean__axioms.ET A E K K A H) /\ ((euclidean__axioms.ET A E K H K A) /\ ((euclidean__axioms.ET A E K A H K) /\ (euclidean__axioms.ET A E K A K H)))) as H29.
---------------------- exact H28.
---------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.ET A E K H K A) /\ ((euclidean__axioms.ET A E K A H K) /\ (euclidean__axioms.ET A E K A K H))) as H31.
----------------------- exact H30.
----------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.ET A E K A H K) /\ (euclidean__axioms.ET A E K A K H)) as H33.
------------------------ exact H32.
------------------------ destruct H33 as [H33 H34].
exact H27.
------------------- assert (* Cut *) (euclidean__axioms.ET H A K A E K) as H27.
-------------------- apply (@euclidean__axioms.axiom__ETsymmetric (A) (E) (K) (H) (A) (K) H26).
-------------------- assert (* Cut *) (euclidean__axioms.ET H A K E A K) as H28.
--------------------- assert (* Cut *) ((euclidean__axioms.ET H A K E K A) /\ ((euclidean__axioms.ET H A K A K E) /\ ((euclidean__axioms.ET H A K E A K) /\ ((euclidean__axioms.ET H A K K E A) /\ (euclidean__axioms.ET H A K K A E))))) as H28.
---------------------- apply (@euclidean__axioms.axiom__ETpermutation (H) (A) (K) (A) (E) (K) H27).
---------------------- assert (* AndElim *) ((euclidean__axioms.ET H A K E K A) /\ ((euclidean__axioms.ET H A K A K E) /\ ((euclidean__axioms.ET H A K E A K) /\ ((euclidean__axioms.ET H A K K E A) /\ (euclidean__axioms.ET H A K K A E))))) as H29.
----------------------- exact H28.
----------------------- destruct H29 as [H29 H30].
assert (* AndElim *) ((euclidean__axioms.ET H A K A K E) /\ ((euclidean__axioms.ET H A K E A K) /\ ((euclidean__axioms.ET H A K K E A) /\ (euclidean__axioms.ET H A K K A E)))) as H31.
------------------------ exact H30.
------------------------ destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.ET H A K E A K) /\ ((euclidean__axioms.ET H A K K E A) /\ (euclidean__axioms.ET H A K K A E))) as H33.
------------------------- exact H32.
------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.ET H A K K E A) /\ (euclidean__axioms.ET H A K K A E)) as H35.
-------------------------- exact H34.
-------------------------- destruct H35 as [H35 H36].
exact H33.
--------------------- assert (* Cut *) (euclidean__axioms.ET E A K H A K) as H29.
---------------------- apply (@euclidean__axioms.axiom__ETsymmetric (H) (A) (K) (E) (A) (K) H28).
---------------------- assert (* Cut *) (euclidean__axioms.EF A K G B F D A K) as H30.
----------------------- assert (* Cut *) ((euclidean__axioms.EF A K G B K F D A) /\ ((euclidean__axioms.EF A K G B D F K A) /\ ((euclidean__axioms.EF A K G B F D A K) /\ ((euclidean__axioms.EF A K G B K A D F) /\ ((euclidean__axioms.EF A K G B D A K F) /\ ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K))))))) as H30.
------------------------ apply (@euclidean__axioms.axiom__EFpermutation (A) (K) (G) (B) (A) (K) (F) (D) H23).
------------------------ assert (* AndElim *) ((euclidean__axioms.EF A K G B K F D A) /\ ((euclidean__axioms.EF A K G B D F K A) /\ ((euclidean__axioms.EF A K G B F D A K) /\ ((euclidean__axioms.EF A K G B K A D F) /\ ((euclidean__axioms.EF A K G B D A K F) /\ ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K))))))) as H31.
------------------------- exact H30.
------------------------- destruct H31 as [H31 H32].
assert (* AndElim *) ((euclidean__axioms.EF A K G B D F K A) /\ ((euclidean__axioms.EF A K G B F D A K) /\ ((euclidean__axioms.EF A K G B K A D F) /\ ((euclidean__axioms.EF A K G B D A K F) /\ ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K)))))) as H33.
-------------------------- exact H32.
-------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.EF A K G B F D A K) /\ ((euclidean__axioms.EF A K G B K A D F) /\ ((euclidean__axioms.EF A K G B D A K F) /\ ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K))))) as H35.
--------------------------- exact H34.
--------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.EF A K G B K A D F) /\ ((euclidean__axioms.EF A K G B D A K F) /\ ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K)))) as H37.
---------------------------- exact H36.
---------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.EF A K G B D A K F) /\ ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K))) as H39.
----------------------------- exact H38.
----------------------------- destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.EF A K G B F K A D) /\ (euclidean__axioms.EF A K G B A D F K)) as H41.
------------------------------ exact H40.
------------------------------ destruct H41 as [H41 H42].
exact H35.
----------------------- assert (* Cut *) (euclidean__axioms.EF F D A K A K G B) as H31.
------------------------ apply (@euclidean__axioms.axiom__EFsymmetric (A) (K) (G) (B) (F) (D) (A) (K) H30).
------------------------ assert (* Cut *) (euclidean__axioms.EF F D A K G B A K) as H32.
------------------------- assert (* Cut *) ((euclidean__axioms.EF F D A K K G B A) /\ ((euclidean__axioms.EF F D A K B G K A) /\ ((euclidean__axioms.EF F D A K G B A K) /\ ((euclidean__axioms.EF F D A K K A B G) /\ ((euclidean__axioms.EF F D A K B A K G) /\ ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K))))))) as H32.
-------------------------- apply (@euclidean__axioms.axiom__EFpermutation (F) (D) (A) (K) (A) (K) (G) (B) H31).
-------------------------- assert (* AndElim *) ((euclidean__axioms.EF F D A K K G B A) /\ ((euclidean__axioms.EF F D A K B G K A) /\ ((euclidean__axioms.EF F D A K G B A K) /\ ((euclidean__axioms.EF F D A K K A B G) /\ ((euclidean__axioms.EF F D A K B A K G) /\ ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K))))))) as H33.
--------------------------- exact H32.
--------------------------- destruct H33 as [H33 H34].
assert (* AndElim *) ((euclidean__axioms.EF F D A K B G K A) /\ ((euclidean__axioms.EF F D A K G B A K) /\ ((euclidean__axioms.EF F D A K K A B G) /\ ((euclidean__axioms.EF F D A K B A K G) /\ ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K)))))) as H35.
---------------------------- exact H34.
---------------------------- destruct H35 as [H35 H36].
assert (* AndElim *) ((euclidean__axioms.EF F D A K G B A K) /\ ((euclidean__axioms.EF F D A K K A B G) /\ ((euclidean__axioms.EF F D A K B A K G) /\ ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K))))) as H37.
----------------------------- exact H36.
----------------------------- destruct H37 as [H37 H38].
assert (* AndElim *) ((euclidean__axioms.EF F D A K K A B G) /\ ((euclidean__axioms.EF F D A K B A K G) /\ ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K)))) as H39.
------------------------------ exact H38.
------------------------------ destruct H39 as [H39 H40].
assert (* AndElim *) ((euclidean__axioms.EF F D A K B A K G) /\ ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K))) as H41.
------------------------------- exact H40.
------------------------------- destruct H41 as [H41 H42].
assert (* AndElim *) ((euclidean__axioms.EF F D A K G K A B) /\ (euclidean__axioms.EF F D A K A B G K)) as H43.
-------------------------------- exact H42.
-------------------------------- destruct H43 as [H43 H44].
exact H37.
------------------------- assert (* Cut *) (euclidean__axioms.EF G B A K F D A K) as H33.
-------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (F) (D) (A) (K) (G) (B) (A) (K) H32).
-------------------------- assert (* Cut *) (euclidean__axioms.EF G B E K F D H K) as H34.
--------------------------- apply (@euclidean__axioms.axiom__cutoff2 (G) (B) (E) (A) (K) (F) (D) (H) (A) (K) (H24) (H25) (H29) H33).
--------------------------- assert (* Cut *) (euclidean__axioms.EF G B E K D F K H) as H35.
---------------------------- assert (* Cut *) ((euclidean__axioms.EF G B E K D H K F) /\ ((euclidean__axioms.EF G B E K K H D F) /\ ((euclidean__axioms.EF G B E K H K F D) /\ ((euclidean__axioms.EF G B E K D F K H) /\ ((euclidean__axioms.EF G B E K K F D H) /\ ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D))))))) as H35.
----------------------------- apply (@euclidean__axioms.axiom__EFpermutation (G) (B) (E) (K) (F) (D) (H) (K) H34).
----------------------------- assert (* AndElim *) ((euclidean__axioms.EF G B E K D H K F) /\ ((euclidean__axioms.EF G B E K K H D F) /\ ((euclidean__axioms.EF G B E K H K F D) /\ ((euclidean__axioms.EF G B E K D F K H) /\ ((euclidean__axioms.EF G B E K K F D H) /\ ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D))))))) as H36.
------------------------------ exact H35.
------------------------------ destruct H36 as [H36 H37].
assert (* AndElim *) ((euclidean__axioms.EF G B E K K H D F) /\ ((euclidean__axioms.EF G B E K H K F D) /\ ((euclidean__axioms.EF G B E K D F K H) /\ ((euclidean__axioms.EF G B E K K F D H) /\ ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D)))))) as H38.
------------------------------- exact H37.
------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.EF G B E K H K F D) /\ ((euclidean__axioms.EF G B E K D F K H) /\ ((euclidean__axioms.EF G B E K K F D H) /\ ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D))))) as H40.
-------------------------------- exact H39.
-------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.EF G B E K D F K H) /\ ((euclidean__axioms.EF G B E K K F D H) /\ ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D)))) as H42.
--------------------------------- exact H41.
--------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.EF G B E K K F D H) /\ ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D))) as H44.
---------------------------------- exact H43.
---------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.EF G B E K H D F K) /\ (euclidean__axioms.EF G B E K F K H D)) as H46.
----------------------------------- exact H45.
----------------------------------- destruct H46 as [H46 H47].
exact H42.
---------------------------- assert (* Cut *) (euclidean__axioms.EF D F K H G B E K) as H36.
----------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (G) (B) (E) (K) (D) (F) (K) (H) H35).
----------------------------- assert (* Cut *) (euclidean__axioms.EF D F K H K G B E) as H37.
------------------------------ assert (* Cut *) ((euclidean__axioms.EF D F K H B E K G) /\ ((euclidean__axioms.EF D F K H K E B G) /\ ((euclidean__axioms.EF D F K H E K G B) /\ ((euclidean__axioms.EF D F K H B G K E) /\ ((euclidean__axioms.EF D F K H K G B E) /\ ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B))))))) as H37.
------------------------------- apply (@euclidean__axioms.axiom__EFpermutation (D) (F) (K) (H) (G) (B) (E) (K) H36).
------------------------------- assert (* AndElim *) ((euclidean__axioms.EF D F K H B E K G) /\ ((euclidean__axioms.EF D F K H K E B G) /\ ((euclidean__axioms.EF D F K H E K G B) /\ ((euclidean__axioms.EF D F K H B G K E) /\ ((euclidean__axioms.EF D F K H K G B E) /\ ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B))))))) as H38.
-------------------------------- exact H37.
-------------------------------- destruct H38 as [H38 H39].
assert (* AndElim *) ((euclidean__axioms.EF D F K H K E B G) /\ ((euclidean__axioms.EF D F K H E K G B) /\ ((euclidean__axioms.EF D F K H B G K E) /\ ((euclidean__axioms.EF D F K H K G B E) /\ ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B)))))) as H40.
--------------------------------- exact H39.
--------------------------------- destruct H40 as [H40 H41].
assert (* AndElim *) ((euclidean__axioms.EF D F K H E K G B) /\ ((euclidean__axioms.EF D F K H B G K E) /\ ((euclidean__axioms.EF D F K H K G B E) /\ ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B))))) as H42.
---------------------------------- exact H41.
---------------------------------- destruct H42 as [H42 H43].
assert (* AndElim *) ((euclidean__axioms.EF D F K H B G K E) /\ ((euclidean__axioms.EF D F K H K G B E) /\ ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B)))) as H44.
----------------------------------- exact H43.
----------------------------------- destruct H44 as [H44 H45].
assert (* AndElim *) ((euclidean__axioms.EF D F K H K G B E) /\ ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B))) as H46.
------------------------------------ exact H45.
------------------------------------ destruct H46 as [H46 H47].
assert (* AndElim *) ((euclidean__axioms.EF D F K H E B G K) /\ (euclidean__axioms.EF D F K H G K E B)) as H48.
------------------------------------- exact H47.
------------------------------------- destruct H48 as [H48 H49].
exact H46.
------------------------------ assert (* Cut *) (euclidean__axioms.EF K G B E D F K H) as H38.
------------------------------- apply (@euclidean__axioms.axiom__EFsymmetric (D) (F) (K) (H) (K) (G) (B) (E) H37).
------------------------------- exact H38.
Qed.
