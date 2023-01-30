Require Export logic.
Parameter Point : Type.
Parameter Circle : Type.
Parameter Cong : euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> Prop.
Parameter BetS : euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> Prop.
Parameter PA : euclidean__axioms.Point.
Parameter PB : euclidean__axioms.Point.
Parameter PC : euclidean__axioms.Point.
Parameter CI : euclidean__axioms.Circle -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> Prop.
Definition neq (A : euclidean__axioms.Point) (B : euclidean__axioms.Point)  := ~(A = B).
Definition TE (A : euclidean__axioms.Point) (B : euclidean__axioms.Point) (C : euclidean__axioms.Point)  := ~((euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq B C) /\ (~(euclidean__axioms.BetS A B C)))).
Definition nCol (A : euclidean__axioms.Point) (B : euclidean__axioms.Point) (C : euclidean__axioms.Point)  := (euclidean__axioms.neq A B) /\ ((euclidean__axioms.neq A C) /\ ((euclidean__axioms.neq B C) /\ ((~(euclidean__axioms.BetS A B C)) /\ ((~(euclidean__axioms.BetS A C B)) /\ (~(euclidean__axioms.BetS B A C)))))).
Definition Col (A : euclidean__axioms.Point) (B : euclidean__axioms.Point) (C : euclidean__axioms.Point)  := (A = B) \/ ((A = C) \/ ((B = C) \/ ((euclidean__axioms.BetS B A C) \/ ((euclidean__axioms.BetS A B C) \/ (euclidean__axioms.BetS A C B))))).
Definition Cong__3 (A : euclidean__axioms.Point) (B : euclidean__axioms.Point) (C : euclidean__axioms.Point) (a : euclidean__axioms.Point) (b : euclidean__axioms.Point) (c : euclidean__axioms.Point)  := (euclidean__axioms.Cong A B a b) /\ ((euclidean__axioms.Cong B C b c) /\ (euclidean__axioms.Cong A C a c)).
Definition TS (P : euclidean__axioms.Point) (A : euclidean__axioms.Point) (B : euclidean__axioms.Point) (Q : euclidean__axioms.Point)  := exists X, (euclidean__axioms.BetS P X Q) /\ ((euclidean__axioms.Col A B X) /\ (euclidean__axioms.nCol A B P)).
Definition Triangle (A : euclidean__axioms.Point) (B : euclidean__axioms.Point) (C : euclidean__axioms.Point)  := euclidean__axioms.nCol A B C.
Definition OnCirc (B : euclidean__axioms.Point) (J : euclidean__axioms.Circle)  := exists X Y U, (euclidean__axioms.CI J U X Y) /\ (euclidean__axioms.Cong U B X Y).
Definition InCirc (P : euclidean__axioms.Point) (J : euclidean__axioms.Circle)  := exists X Y U V W, (euclidean__axioms.CI J U V W) /\ ((P = U) \/ ((euclidean__axioms.BetS U Y X) /\ ((euclidean__axioms.Cong U X V W) /\ (euclidean__axioms.Cong U P U Y)))).
Definition OutCirc (P : euclidean__axioms.Point) (J : euclidean__axioms.Circle)  := exists X U V W, (euclidean__axioms.CI J U V W) /\ ((euclidean__axioms.BetS U X P) /\ (euclidean__axioms.Cong U X V W)).
Axiom cn__congruencetransitive : forall B C D E P Q, (euclidean__axioms.Cong P Q B C) -> ((euclidean__axioms.Cong P Q D E) -> (euclidean__axioms.Cong B C D E)).
Axiom cn__congruencereflexive : forall A B, euclidean__axioms.Cong A B A B.
Axiom cn__equalityreverse : forall A B, euclidean__axioms.Cong A B B A.
Axiom cn__sumofparts : forall A B C a b c, (euclidean__axioms.Cong A B a b) -> ((euclidean__axioms.Cong B C b c) -> ((euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS a b c) -> (euclidean__axioms.Cong A C a c)))).
Axiom cn__stability : forall A B, (~(euclidean__axioms.neq A B)) -> (A = B).
Axiom axiom__circle__center__radius : forall A B C J P, (euclidean__axioms.CI J A B C) -> ((euclidean__axioms.OnCirc P J) -> (euclidean__axioms.Cong A P B C)).
Axiom axiom__lower__dim : euclidean__axioms.nCol euclidean__axioms.PA euclidean__axioms.PB euclidean__axioms.PC.
Axiom axiom__betweennessidentity : forall A B, ~(euclidean__axioms.BetS A B A).
Axiom axiom__betweennesssymmetry : forall A B C, (euclidean__axioms.BetS A B C) -> (euclidean__axioms.BetS C B A).
Axiom axiom__innertransitivity : forall A B C D, (euclidean__axioms.BetS A B D) -> ((euclidean__axioms.BetS B C D) -> (euclidean__axioms.BetS A B C)).
Axiom axiom__connectivity : forall A B C D, (euclidean__axioms.BetS A B D) -> ((euclidean__axioms.BetS A C D) -> ((~(euclidean__axioms.BetS A B C)) -> ((~(euclidean__axioms.BetS A C B)) -> (B = C)))).
Axiom axiom__nocollapse : forall A B C D, (euclidean__axioms.neq A B) -> ((euclidean__axioms.Cong A B C D) -> (euclidean__axioms.neq C D)).
Axiom axiom__5__line : forall A B C D a b c d, (euclidean__axioms.Cong B C b c) -> ((euclidean__axioms.Cong A D a d) -> ((euclidean__axioms.Cong B D b d) -> ((euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS a b c) -> ((euclidean__axioms.Cong A B a b) -> (euclidean__axioms.Cong D C d c)))))).
Axiom postulate__Pasch__inner : forall A B C P Q, (euclidean__axioms.BetS A P C) -> ((euclidean__axioms.BetS B Q C) -> ((euclidean__axioms.nCol A C B) -> (exists X, (euclidean__axioms.BetS A X Q) /\ (euclidean__axioms.BetS B X P)))).
Axiom postulate__Pasch__outer : forall A B C P Q, (euclidean__axioms.BetS A P C) -> ((euclidean__axioms.BetS B C Q) -> ((euclidean__axioms.nCol B Q A) -> (exists X, (euclidean__axioms.BetS A X Q) /\ (euclidean__axioms.BetS B P X)))).
Axiom postulate__Euclid2 : forall A B, (euclidean__axioms.neq A B) -> (exists X, euclidean__axioms.BetS A B X).
Axiom postulate__Euclid3 : forall A B, (euclidean__axioms.neq A B) -> (exists X, euclidean__axioms.CI X A A B).
Axiom postulate__line__circle : forall A B C K P Q, (euclidean__axioms.CI K C P Q) -> ((euclidean__axioms.InCirc B K) -> ((euclidean__axioms.neq A B) -> (exists X Y, (euclidean__axioms.Col A B X) /\ ((euclidean__axioms.BetS A B Y) /\ ((euclidean__axioms.OnCirc X K) /\ ((euclidean__axioms.OnCirc Y K) /\ (euclidean__axioms.BetS X B Y))))))).
Axiom postulate__circle__circle : forall C D F G J K P Q R S, (euclidean__axioms.CI J C R S) -> ((euclidean__axioms.InCirc P J) -> ((euclidean__axioms.OutCirc Q J) -> ((euclidean__axioms.CI K D F G) -> ((euclidean__axioms.OnCirc P K) -> ((euclidean__axioms.OnCirc Q K) -> (exists X, (euclidean__axioms.OnCirc X J) /\ (euclidean__axioms.OnCirc X K))))))).
Axiom postulate__Euclid5 : forall a p q r s t, (euclidean__axioms.BetS r t s) -> ((euclidean__axioms.BetS p t q) -> ((euclidean__axioms.BetS r a q) -> ((euclidean__axioms.Cong p t q t) -> ((euclidean__axioms.Cong t r t s) -> ((euclidean__axioms.nCol p q s) -> (exists X, (euclidean__axioms.BetS p a X) /\ (euclidean__axioms.BetS s q X))))))).
Parameter EF : euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> Prop.
Parameter ET : euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> euclidean__axioms.Point -> Prop.
Axiom axiom__congruentequal : forall A B C a b c, (euclidean__axioms.Cong__3 A B C a b c) -> (euclidean__axioms.ET A B C a b c).
Axiom axiom__ETpermutation : forall A B C a b c, (euclidean__axioms.ET A B C a b c) -> ((euclidean__axioms.ET A B C b c a) /\ ((euclidean__axioms.ET A B C a c b) /\ ((euclidean__axioms.ET A B C b a c) /\ ((euclidean__axioms.ET A B C c b a) /\ (euclidean__axioms.ET A B C c a b))))).
Axiom axiom__ETsymmetric : forall A B C a b c, (euclidean__axioms.ET A B C a b c) -> (euclidean__axioms.ET a b c A B C).
Axiom axiom__EFpermutation : forall A B C D a b c d, (euclidean__axioms.EF A B C D a b c d) -> ((euclidean__axioms.EF A B C D b c d a) /\ ((euclidean__axioms.EF A B C D d c b a) /\ ((euclidean__axioms.EF A B C D c d a b) /\ ((euclidean__axioms.EF A B C D b a d c) /\ ((euclidean__axioms.EF A B C D d a b c) /\ ((euclidean__axioms.EF A B C D c b a d) /\ (euclidean__axioms.EF A B C D a d c b))))))).
Axiom axiom__halvesofequals : forall A B C D a b c d, (euclidean__axioms.ET A B C B C D) -> ((euclidean__axioms.TS A B C D) -> ((euclidean__axioms.ET a b c b c d) -> ((euclidean__axioms.TS a b c d) -> ((euclidean__axioms.EF A B D C a b d c) -> (euclidean__axioms.ET A B C a b c))))).
Axiom axiom__EFsymmetric : forall A B C D a b c d, (euclidean__axioms.EF A B C D a b c d) -> (euclidean__axioms.EF a b c d A B C D).
Axiom axiom__EFtransitive : forall A B C D P Q R S a b c d, (euclidean__axioms.EF A B C D a b c d) -> ((euclidean__axioms.EF a b c d P Q R S) -> (euclidean__axioms.EF A B C D P Q R S)).
Axiom axiom__ETtransitive : forall A B C P Q R a b c, (euclidean__axioms.ET A B C a b c) -> ((euclidean__axioms.ET a b c P Q R) -> (euclidean__axioms.ET A B C P Q R)).
Axiom axiom__cutoff1 : forall A B C D E a b c d e, (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS a b c) -> ((euclidean__axioms.BetS E D C) -> ((euclidean__axioms.BetS e d c) -> ((euclidean__axioms.ET B C D b c d) -> ((euclidean__axioms.ET A C E a c e) -> (euclidean__axioms.EF A B D E a b d e)))))).
Axiom axiom__cutoff2 : forall A B C D E a b c d e, (euclidean__axioms.BetS B C D) -> ((euclidean__axioms.BetS b c d) -> ((euclidean__axioms.ET C D E c d e) -> ((euclidean__axioms.EF A B D E a b d e) -> (euclidean__axioms.EF A B C E a b c e)))).
Axiom axiom__paste1 : forall A B C D E a b c d e, (euclidean__axioms.BetS A B C) -> ((euclidean__axioms.BetS a b c) -> ((euclidean__axioms.BetS E D C) -> ((euclidean__axioms.BetS e d c) -> ((euclidean__axioms.ET B C D b c d) -> ((euclidean__axioms.EF A B D E a b d e) -> (euclidean__axioms.ET A C E a c e)))))).
Axiom axiom__deZolt1 : forall B C D E, (euclidean__axioms.BetS B E D) -> (~(euclidean__axioms.ET D B C E B C)).
Axiom axiom__deZolt2 : forall A B C E F, (euclidean__axioms.Triangle A B C) -> ((euclidean__axioms.BetS B E A) -> ((euclidean__axioms.BetS B F C) -> (~(euclidean__axioms.ET A B C E B F)))).
Axiom axiom__paste2 : forall A B C D E M a b c d e m, (euclidean__axioms.BetS B C D) -> ((euclidean__axioms.BetS b c d) -> ((euclidean__axioms.ET C D E c d e) -> ((euclidean__axioms.EF A B C E a b c e) -> ((euclidean__axioms.BetS A M D) -> ((euclidean__axioms.BetS B M E) -> ((euclidean__axioms.BetS a m d) -> ((euclidean__axioms.BetS b m e) -> (euclidean__axioms.EF A B D E a b d e)))))))).
Axiom axiom__paste3 : forall A B C D M a b c d m, (euclidean__axioms.ET A B C a b c) -> ((euclidean__axioms.ET A B D a b d) -> ((euclidean__axioms.BetS C M D) -> (((euclidean__axioms.BetS A M B) \/ ((A = M) \/ (M = B))) -> ((euclidean__axioms.BetS c m d) -> (((euclidean__axioms.BetS a m b) \/ ((a = m) \/ (m = b))) -> (euclidean__axioms.EF A C B D a c b d)))))).
Axiom axiom__paste4 : forall A B C D F G H J K L M P e m, (euclidean__axioms.EF A B m D F K H G) -> ((euclidean__axioms.EF D B e C G H M L) -> ((euclidean__axioms.BetS A P C) -> ((euclidean__axioms.BetS B P D) -> ((euclidean__axioms.BetS K H M) -> ((euclidean__axioms.BetS F G L) -> ((euclidean__axioms.BetS B m D) -> ((euclidean__axioms.BetS B e C) -> ((euclidean__axioms.BetS F J M) -> ((euclidean__axioms.BetS K J L) -> (euclidean__axioms.EF A B C D F K M L)))))))))).
