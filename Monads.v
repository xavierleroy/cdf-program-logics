(** Hoare monads and Dijkstra monads *)

From Coq Require Import Program ZArith.
From CDF Require Hoare Separation Delay.

Ltac inv H := inversion H; clear H; subst.

(** * Hoare monads *)

(** ** The generic interface *)

Module Type HOAREMONAD.
  Parameter PRE: Type.
  Definition POST (A: Type) := A -> PRE.
  Parameter M: forall (P: PRE) (A: Type) (Q: POST A), Type.
  Parameter ret:
    forall {A: Type} (Q: POST A) (v: A), M (Q v) A Q.
  Parameter bind:
    forall {A B: Type} (P: PRE) (Q: POST A) (R: POST B),
           M P A Q -> (forall (v: A), M (Q v) B R) -> M P B R.
  Parameter implies: PRE -> PRE -> Prop.
  Parameter consequence_pre:
    forall {A: Type} (P P': PRE) (Q: POST A),
           implies P' P -> M P A Q -> M P' A Q.
  Parameter consequence_post:
    forall {A: Type} (P: PRE) (Q Q': POST A),
           (forall v, implies (Q v) (Q' v))-> M P A Q -> M P A Q'.
End HOAREMONAD.

(** ** The Hoare monad of pure computations *)

Module HPure <: HOAREMONAD.

Definition PRE := Prop.
Definition POST (A: Type) := A -> PRE.
Definition M (P: PRE) (A: Type) (Q: POST A) := P -> { a : A | Q a }.

Definition ret {A: Type} (Q: POST A) (v: A) : M (Q v) A Q :=
  fun p => exist _ v p.

Definition bind {A B: Type}
                (P: PRE) (Q: POST A) (R: POST B)
                (a: M P A Q) (f: forall (v: A), M (Q v) B R) : M P B R :=
  fun p => let '(exist _ b r) := a p in f b r.

Definition implies (P P': PRE) := P -> P'.

Definition consequence_pre 
     {A: Type} (P P': PRE) (Q: POST A) (IMP: implies P' P) (m: M P A Q) : M P' A Q :=
  fun p' => m (IMP p').

Program Definition consequence_post 
     {A: Type} (P: PRE) (Q Q': POST A) (IMP: forall v, implies (Q v) (Q' v)) (m: M P A Q) : M P A Q' :=
  fun p => m p.
Next Obligation.
  destruct (m p); cbn. apply IMP; auto.
Qed.

End HPure.

(** ** The Hoare monad of possibly-diverging computations *)

Module HDiv <: HOAREMONAD.

Import Delay.

Definition PRE := Prop.
Definition POST (A: Type) := A -> PRE.
Definition M (P: PRE) (A: Type) (Q: POST A) := P -> { d : delay A | safe Q d }.

Program Definition ret {A: Type} (Q: POST A) (v: A) : M (Q v) A Q :=
  fun _ => now v.
Next Obligation.
  constructor; auto.
Qed.

Section BIND.

Context {A B: Type}
        (P: PRE) (Q: POST A) (R: POST B)
        (a: M P A Q) (f: forall (v: A), M (Q v) B R).

CoFixpoint bind_aux (d: delay A) : safe Q d -> delay B :=
  match d with
  | now v => fun SAFE => later (proj1_sig (f v (safe_inv_now _ _ SAFE)))
  | later d => fun SAFE => later (bind_aux d (safe_inv_later _ _ SAFE))
  end.

Lemma safe_bind_aux:
  forall (d: delay A) (s: safe Q d), safe R (bind_aux d s).
Proof.
  cofix COH; intros. unroll_delay (bind_aux d s); destruct d.
- destruct (f a0 (safe_inv_now Q a0 s)) as (d1 & s1); cbn. constructor; auto.
- constructor. apply COH. 
Qed. 

Definition bind : M P B R :=
  fun p => let '(exist _ d s) := a p in exist _ (bind_aux d s) (safe_bind_aux d s).

End BIND.

Definition implies (P P': PRE) := P -> P'.

Definition consequence_pre 
     {A: Type} (P P': PRE) (Q: POST A) (IMP: implies P' P) (m: M P A Q) : M P' A Q :=
  fun p' => m (IMP p').

Program Definition consequence_post 
     {A: Type} (P: PRE) (Q Q': POST A) (IMP: forall v, implies (Q v) (Q' v)) (m: M P A Q) : M P A Q' :=
  fun p => m p.
Next Obligation.
  destruct (m p); cbn. apply safe_consequence with Q; auto.
Qed.

(** A specific operation of the DIV monad: a [repeat...until] unbounded loop.
   [iter f x] is such that

- [iter f x = y] if [f x] terminates with [inr y]
- [iter f x = iter f x'] if [f x] terminates with [inl x'].
*)

Section ITER.

Context {A B: Type} (P: A -> PRE) (Q: POST B).

Let R : POST (A + B) := fun ab => match ab with inl a => P a | inr b => Q b end.

Context (f: forall (a: A), M (P a) (A + B) R).

CoFixpoint iter_aux (d: delay (A + B)) : safe R d -> delay B :=
  match d with
  | now (inl a) => fun SAFE => let '(exist _ d' s') := f a (safe_inv_now _ _ SAFE) in later (iter_aux d' s')
  | now (inr b) => fun SAFE => now b
  | later d => fun SAFE => later (iter_aux d (safe_inv_later _ _ SAFE))
  end.

Lemma safe_iter_aux:
  forall (d: delay (A + B)) (s: safe R d), safe Q (iter_aux d s).
Proof.
  cofix COINDHYP; intros. unroll_delay (iter_aux d s); destruct d as [[a | b] | d].
- destruct f as [ab' s']. constructor. apply COINDHYP.
- apply safe_inv_now in s. constructor. auto.
- constructor. apply COINDHYP.
Qed.

Program Definition iter (x: A) : M (P x) B Q :=
  fun p => iter_aux (now (inl x)) _.
Next Obligation.
  constructor. auto.
Qed.
Next Obligation.
  apply safe_iter_aux.
Qed.

End ITER.

End HDiv.

(** ** The Hoare monad for mutable state *)

Module HST <: HOAREMONAD.

Import Separation.

Definition PRE := heap -> Prop.
Definition POST (A: Type) := A -> PRE.

Definition M (P: PRE) (A: Type) (Q: POST A) : Type :=
  forall h, P h -> { a_h : A * heap | Q (fst a_h) (snd a_h) }.

Program Definition ret {A: Type} (Q: POST A) (v: A) : M (Q v) A Q
  := fun h _ => (v, h).

Program Definition bind {A B: Type}
  (P: PRE) (Q: POST A) (R: POST B)
  (a: M P A Q) (f: forall (v: A), M (Q v) B R) : M P B R :=
  fun h p => let '(v, h') := a h p in f v h' _.
Next Obligation.
  destruct (a h p) as [[v1 h1] p1]; simpl in *. inv Heq_anonymous. auto.
Qed.

Definition implies (P P': PRE) := P -->> P'.

Definition consequence_pre 
     {A: Type} (P P': PRE) (Q: POST A) (IMP: implies P' P) (m: M P A Q) : M P' A Q :=
  fun h p' => m h (IMP h p').

Program Definition consequence_post 
     {A: Type} (P: PRE) (Q Q': POST A) (IMP: forall v, implies (Q v) (Q' v)) (m: M P A Q) : M P A Q' :=
  fun h p => m h p.
Next Obligation.
  destruct (m h p) as [[v h'] q]; cbn. apply IMP; auto.
Qed.

Definition consequence 
     {A: Type} (P P': PRE) (Q Q': POST A)
               (IMP1: implies P' P) (IMP2: forall v, implies (Q v) (Q' v)) (m: M P A Q) : M P' A Q' :=
  consequence_pre _ _ _ IMP1 (consequence_post _ _ _ IMP2 m).

Program Definition get (l: addr) : 
  forall v R, M (contains l v ** R) Z (fun v' => (v' = v) //\\ contains l v ** R) :=
  fun v R h p => match h l with Some v' => (v', h) | None => _ end.
Next Obligation.
  split; auto.
  destruct p as (h1 & h2 & p1 & p2 & D & U).
  rewrite U in Heq_anonymous. cbn in Heq_anonymous.
  rewrite ! p1, hupdate_same in Heq_anonymous.
  congruence.
Qed.
Next Obligation.
  exfalso.
  destruct p as (h1 & h2 & p1 & p2 & D & U).
  rewrite U in Heq_anonymous. cbn in Heq_anonymous.
  rewrite ! p1, hupdate_same in Heq_anonymous.
  congruence.
Qed.

Program Definition set (l: addr) (v: Z) :
  forall R, M (valid l ** R) unit (fun _ => contains l v ** R) :=
  fun R h p => (tt, hupdate l v h).
Next Obligation.
  destruct p as (h1 & h2 & p1 & p2 & D & U). destruct p1 as (v0 & p1). rewrite p1 in *.
  exists (hupdate l v hempty), h2.
  split. red; auto.
  split. auto.
  split. red; intros x; cbn. specialize (D x); cbn in D.
    destruct (Z.eq_dec l x); intuition congruence.
  rewrite U. apply heap_extensionality; intros x. cbn. destruct (Z.eq_dec l x); auto.
Qed.

End HST.

(** ** The Hoare monad for mutable state in separation logic style *)

Module HSep.

Import Separation.

Definition PRE := heap -> Prop.
Definition POST (A: Type) := A -> PRE.

Definition M (P: PRE) (A: Type) (Q: POST A) : Type :=
  forall (R: assertion), HST.M (P ** R) A (fun v => Q v ** R).

Definition ret {A: Type} (Q: POST A) (v: A) : M (Q v) A Q :=
  fun R => HST.ret (fun v => Q v ** R) v.

Definition bind {A B: Type}
  (P: assertion) (Q: A -> assertion) (R: B -> assertion)
  (a: M P A Q) (f: forall (v: A), M (Q v) B R) : M P B R :=
  fun F => HST.bind (P ** F) (fun v => Q v ** F) (fun v => R v ** F)
                        (a F) (fun v => f v F).

Definition implies (P P': PRE) := P -->> P'.

Program Definition consequence_pre 
     {A: Type} (P P': PRE) (Q: POST A) (IMP: implies P' P) (m: M P A Q) : M P' A Q :=
  fun R => HST.consequence_pre (P ** R) (P' ** R) (fun v => Q v ** R) _ (m R).
Next Obligation.
  apply sepconj_imp_l; auto.
Qed.

Program Definition consequence_post 
     {A: Type} (P: PRE) (Q Q': POST A) (IMP: forall v, implies (Q v) (Q' v)) (m: M P A Q) : M P A Q' :=
  fun R => HST.consequence_post (P ** R) (fun v => Q v ** R) (fun v => Q' v ** R) _ (m R).
Next Obligation.
  apply sepconj_imp_l. apply IMP.
Qed.

Definition consequence 
     {A: Type} (P P': PRE) (Q Q': POST A)
               (IMP1: implies P' P) (IMP2: forall v, implies (Q v) (Q' v)) (m: M P A Q) : M P' A Q' :=
  consequence_pre _ _ _ IMP1 (consequence_post _ _ _ IMP2 m).

Program Definition frame
     {A: Type} (R: PRE) (P: PRE) (Q: POST A) (m: M P A Q) : M (P ** R) A (fun v => Q v ** R) :=
  fun R' => HST.consequence _ _ _ _ _ _ (m (R ** R')).
Next Obligation.
  rewrite sepconj_assoc. hnf; auto.
Qed.
Next Obligation.
  rewrite sepconj_assoc. hnf; auto.
Qed.

Program Definition get (l: addr) : 
  forall v, M (contains l v) Z (fun v' => (v' = v) //\\ contains l v) :=
  fun v R => HST.consequence_post _ _ _ _ (HST.get l v R).
Next Obligation.
  rewrite lift_pureconj. hnf; auto.
Qed.

Program Definition set (l: addr) (v: Z) :
  M (valid l) unit (fun _ => contains l v) :=
  fun R => HST.set l v R.

End HSep.

(** * Dijkstra monads *)

(** ** The generic interface *)

Module Type DIJKSTRAMONAD.
  Parameter PRE: Type.
  Parameter POST: forall (A: Type), Type.
  Definition TRANSF (A: Type) := POST A -> PRE.
  Parameter M: forall (A: Type) (W: TRANSF A), Type.
  Parameter RET: forall {A: Type} (v: A), TRANSF A.
  Parameter ret: forall {A: Type} (v: A), M A (RET v).
  Parameter BIND:
    forall {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B), TRANSF B.
  Parameter bind:
    forall {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B),
    M A W1 -> (forall (v: A), M B (W2 v)) -> M B (BIND W1 W2).
End DIJKSTRAMONAD.

(** ** The Dijkstra monad of pure computations *)

Module DPure <: DIJKSTRAMONAD.

Definition PRE := Prop.
Definition POST (A: Type) := A -> PRE.
Definition TRANSF (A: Type) := POST A -> PRE.

Definition M (A: Type) (W: TRANSF A) : Type :=
  forall Q, W Q -> { r: A | Q r}.

Definition RET {A: Type} (v: A) : TRANSF A := fun Q => Q v.

Definition ret {A: Type} (v: A) : M A (RET v) :=
  fun Q p => exist _ v p.

Definition BIND {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B) : TRANSF B :=
  fun Q => W1 (fun x => W2 x Q).

Definition bind {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B)
                (m: M A W1) (f: forall (v: A), M B (W2 v)) : M B (BIND W1 W2) :=
  fun Q p => let '(exist _ x q) := m _ p in f x Q q.

End DPure.

(** ** The Dijkstra monad of diverging computations *)

Module DDiv <: DIJKSTRAMONAD.

Definition PRE := Prop.
Definition POST (A: Type) := A -> PRE.
Definition TRANSF (A: Type) := POST A -> PRE.

Definition M (A: Type) (W: TRANSF A) : Type := forall Q, HDiv.M (W Q) A Q.

Definition RET {A: Type} (v: A) : TRANSF A := fun Q => Q v.

Definition ret {A: Type} (v: A) : M A (RET v) := fun Q => HDiv.ret Q v.

Definition BIND {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B) : TRANSF B :=
  fun Q => W1 (fun x => W2 x Q).

Definition bind {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B)
                (m: M A W1) (f: forall (v: A), M B (W2 v)) : M B (BIND W1 W2) :=
  fun Q => HDiv.bind (BIND W1 W2 Q) (fun x => W2 x Q) Q (m (fun x => W2 x Q)) (fun x => f x Q).

End DDiv.

(** Lifting pure computations to the [DDiv] monad. *)

Definition DIV_of_PURE {A: Type} (W: DPure.TRANSF A) : DDiv.TRANSF A := W.

Definition div_of_pure {A: Type} {W: DPure.TRANSF A} (m: DPure.M A W)
  : DDiv.M A (DIV_of_PURE W)
  := fun Q p => let '(exist _ v q) := m Q p in (DDiv.ret v Q q).

(** ** The Dijkstra monad of mutable state *)

Module DST <: DIJKSTRAMONAD.

Import Separation.

Definition PRE := heap -> Prop.
Definition POST (A: Type) := A -> PRE.
Definition TRANSF (A: Type) := POST A -> PRE.

Definition M (A: Type) (W: TRANSF A) : Type := forall Q, HST.M (W Q) A Q.

Definition RET {A: Type} (v: A) : TRANSF A := fun Q => Q v.

Definition ret {A: Type} (v: A) : M A (RET v) := fun Q => HST.ret Q v.

Definition BIND {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B) : TRANSF B :=
  fun Q => W1 (fun x => W2 x Q).

Definition bind {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B)
                (m: M A W1) (f: forall (v: A), M B (W2 v)) : M B (BIND W1 W2) :=
  fun Q => HST.bind (BIND W1 W2 Q) (fun x => W2 x Q) Q (m (fun x => W2 x Q)) (fun x => f x Q).

Definition GET (l: addr) : TRANSF Z :=
  fun Q (h: heap) => match h l with Some v => Q v h | None => False end.

Program Definition get (l: addr) : M Z (GET l) :=
  fun Q h p => match h l with Some v => (v, h) | None => _ end.
Next Obligation.
  red in p. rewrite <- Heq_anonymous in p. auto.
Qed.
Next Obligation.
  exfalso. red in p. rewrite <- Heq_anonymous in p. auto.
Qed.

Definition SET (l: addr) (v: Z) : TRANSF unit :=
  fun Q (h: heap) => h l <> None /\ Q tt (hupdate l v h).

Program Definition set (l: addr) (v: Z) : M unit (SET l v) :=
  fun Q h p => (tt, hupdate l v h).
Next Obligation.
  apply p.
Qed.

End DST.

(** Lifting pure computations to the [DST] monad. *)

Definition ST_of_PURE {A: Type} (W: DPure.TRANSF A) : DST.TRANSF A :=
  fun (Q: DST.POST A) h => W (fun a => Q a h).

Program Definition st_of_pure {A: Type} {W: DPure.TRANSF A} (m: DPure.M A W)
  : DST.M A (ST_of_PURE W)
  := fun Q h p => (m (fun a => Q a h) p, h).
Next Obligation.
  destruct m; cbn. auto.
Qed.

(** ** The Dijkstra monad of exceptions *)

Parameter exn: Type.

Module DExn <: DIJKSTRAMONAD.

Definition PRE := Prop.
Definition POST (A: Type) := A + exn -> PRE.
Definition TRANSF (A: Type) := POST A -> PRE.

Definition M (A: Type) (W: TRANSF A) : Type :=
  forall Q, W Q -> { r: A + exn | Q r}.

Definition RET {A: Type} (v: A) : TRANSF A := fun Q => Q (inl v).

Definition ret {A: Type} (v: A) : M A (RET v) :=
  fun Q p => exist _ (inl v) p.

Definition BIND {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B) : TRANSF B :=
  fun Q => W1 (fun x => match x with inl v => W2 v Q | inr e => Q (inr e) end).

Program Definition bind {A B: Type} (W1: TRANSF A) (W2: A -> TRANSF B)
                   (m: M A W1) (f: forall (v: A), M B (W2 v)) : M B (BIND W1 W2) :=
  fun Q p => match m _ p with inl v => f v Q _ | inr e => inr e end.
Next Obligation.
  red in p. destruct m as [r q]. cbn in Heq_anonymous. subst r. auto.
Qed.
Next Obligation.
  red in p. destruct m as [r q]. cbn in Heq_anonymous. subst r. auto.
Qed.  

Definition RAISE (A: Type) (e: exn) : TRANSF A := fun Q => Q (inr e).

Definition raise (A: Type) (e: exn) : M A (RAISE A e) :=
  fun Q p => exist _ (inr e) p.

End DExn.

(** Lifting pure computations to the [DExn] monad. *)

Definition EXN_of_PURE {A: Type} (W: DPure.TRANSF A) : DExn.TRANSF A :=
  fun (Q: DExn.POST A) => W (fun a => Q (inl a)).

Program Definition exn_of_pure {A: Type} {W: DPure.TRANSF A} (m: DPure.M A W)
  : DExn.M A (EXN_of_PURE W)
  := fun Q p => inl (proj1_sig (m (fun a => Q (inl a)) p)).
Next Obligation.
  destruct m; cbn. auto.
Qed.

