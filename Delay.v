(** The [delay] type and Capretta's partiality monad *)

(** The type [delay A] represents computations that produce a result
    of type [A] if they terminate, but can also diverge. *)

CoInductive delay (A: Type) :=
  | now : A -> delay A
  | later : delay A -> delay A.

Arguments now [A].
Arguments later [A].

Lemma u_delay:
  forall {A: Type} (x: delay A),
  x = match x with now v => now v | later y => later y end.
Proof. destruct x; auto. Qed.

Ltac unroll_delay X := rewrite (u_delay X); cbn.

(** The monad structure. *)

Definition ret := now.

CoFixpoint bind {A B: Type} (d: delay A) (f: A -> delay B) :=
  match d with
  | now v => later (f v)
  | later d' => later (bind d' f)
  end.

(** [safe Q d] means: if the computation [d] terminates,
    its value satisfies predicate [Q].  It's like a postcondition
    in a weak Hoare triple. *)

CoInductive safe {A: Type} (Q: A -> Prop) : delay A -> Prop :=
  | safe_now: forall a, Q a -> safe Q (now a)
  | safe_later: forall d, safe Q d -> safe Q (later d).

Lemma safe_inv_now: forall {A: Type} (Q: A -> Prop) v,
  safe Q (now v) -> Q v.
Proof.
  intros. inversion H. auto.
Qed.

Lemma safe_inv_later: forall {A: Type} (Q: A -> Prop) d,
  safe Q (later d) -> safe Q d.
Proof.
  intros. inversion H. auto.
Qed.

Lemma safe_consequence:
  forall {A: Type} (Q1 Q2: A -> Prop),
  (forall a, Q1 a -> Q2 a) ->
  forall (d: delay A), safe Q1 d -> safe Q2 d.
Proof.
  intros until Q2; intros IMP. cofix COINDHYP; destruct 1.
- constructor; auto.
- constructor; auto.
Qed.

Lemma safe_bind:
  forall {A B: Type} (Q1: A -> Prop) (Q2: B -> Prop)
         (d: delay A) (f: A -> delay B),
  safe Q1 d -> (forall v, Q1 v -> safe Q2 (f v)) -> safe Q2 (bind d f).
Proof.
  intros until Q2. cofix COINDHYP; intros.
  unroll_delay (bind d f). destruct d.
- apply safe_inv_now in H. constructor. apply H0. auto.
- apply safe_inv_later in H. constructor. apply COINDHYP; auto.
Qed.
