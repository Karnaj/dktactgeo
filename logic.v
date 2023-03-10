Definition true := True.
Definition false : Prop := False.
Definition False__ind : forall (A:Prop), False -> A := False_ind.
Definition not : Prop -> Prop := not.
Definition and : Prop -> Prop -> Prop := and.
Definition or : Prop -> Prop -> Prop := or.
Definition ex : forall (A:Type), (A -> Prop) -> Prop := ex.
Definition and__ind : forall (A:Prop), forall (B:Prop), forall (P:Prop), (A -> B -> P) -> (and A B) -> P := and_ind.
Definition or__ind : forall (A:Prop), forall (B:Prop), forall (P:Prop), (A -> P) -> (B -> P) -> (or A B) -> P := or_ind.
Definition ex__ind : forall A, forall (P:(A -> Prop)), forall (return_:Prop), (forall (x:A), (P x) -> return_) -> (ex (A) P) -> return_ := ex_ind. 
Definition conj : forall (A:Prop), forall (B:Prop), A -> B -> and A B := conj. 
Definition or__introl : forall (A:Prop), forall (B:Prop), A -> or A B := or_introl.
Definition or__intror : forall (A:Prop), forall (B:Prop), B -> or A B := or_intror.
Definition ex__intro : forall A, forall (P:(A -> Prop)), forall (x:A), (P x) -> ex (A) P := ex_intro.
(* Definition eq : forall (A:Type), A -> A -> Prop := fun (A:Type) => fun (x:A) => fun (y:A) => eq x y. *)
Definition eq : forall (A:Type), A -> A -> Prop := @eq.
Definition eq__refl : forall A, forall (x:A), eq A x x := @eq_refl.
Definition eq__trans : forall A, forall (x:A), forall (y:A), forall (z:A), (eq (A) x y) -> (eq (A) y z) -> eq (A) x z := eq_trans.
Definition eq__ind : forall A, forall (x:A), forall (P:(A -> Prop)), (P x) -> forall (y:A), (eq (A) x y) -> P y := eq_ind.
Definition eq__sym : forall A, forall (x:A), forall (y:A), (eq (A) x y) -> eq (A) y x := eq_sym.
Definition eq__ind__r : forall A, forall (a:A), forall (P:(A -> Prop)), (P a) -> forall (x:A), (eq (A) x a) -> P x := eq_ind_r.
