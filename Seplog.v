(** Separation logic. *)

From Coq Require Import ZArith Lia Bool List.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Sequences Separation.

Local Open Scope Z_scope.

(** * 1. A language of pointers *)

(** We now define a small programming language to work with pointers to
    mutable state.  The language has variables, but these variables are
    immutable.  This in unlike IMP but like ML: mutable variables are
    expressed as immutable pointers (references) to mutable state. *)

(** As in ML too, we blur the distinction between expressions and commands.
    Every command returns a value, which we take to be an integer,
    in addition to possibly performing effects. *)

(** We use higher-order abstract syntax to represent commands in this
    language.  With first-order abstract syntax, a "let" binding
    [let x = a in b] would be represented using the constructor 
<<
    LET: forall (x: ident) (a b: com), com
>>
    With higher-order syntax, we use a Coq function [fun x => b] to
    represent the binding of [x] inside [b]:
<<
    LET: forall (a: com) (b: Z -> com), com
>>
    As a benefit, we can use any Coq expression of type [Z] as a
    pure command of the language, making it unnecessary to define
    syntax and semantics for a specific expression language.
*)

CoInductive com: Type :=
  | PURE (x: Z)                         (**r command without effects *)
  | LET (c: com) (f: Z -> com)          (**r sequencing of commands *)
  | IFTHENELSE (b: Z) (c1 c2: com)      (**r conditional *)
  | ALLOC (sz: nat)                     (**r allocate [sz] words of storage *)
  | GET (l: addr)                       (**r dereference a pointer *)
  | SET (l: addr) (v: Z)                (**r assign through a pointer *)
  | FREE (l: addr)                      (**r free one word of storage *)
  | PICK (n: Z).                        (**r pick a number between 0 and [n] *)

(** Some derived forms. *)

Definition SKIP: com := PURE 0.

Definition SEQ (c1 c2: com) := LET c1 (fun _ => c2).

Definition EITHER (c1 c2: com) := LET (PICK 2) (fun n => IFTHENELSE n c1 c2).

(** Reduction semantics. *)

Inductive red: com * heap -> com * heap -> Prop :=
  | red_pick: forall n i h,
      0 <= i < n ->
      red (PICK n, h) (PURE i, h)
  | red_let_done: forall x f h,
      red (LET (PURE x) f, h) (f x, h)
  | red_let_step: forall c f h c' h',
      red (c, h) (c', h') ->
      red (LET c f, h) (LET c' f, h')
  | red_ifthenelse: forall b c1 c2 h,
      red (IFTHENELSE b c1 c2, h) ((if b =? 0 then c2 else c1), h)
  | red_alloc: forall sz (h: heap) l,
      (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
      l <> 0 ->
      red (ALLOC sz, h) (PURE l, hinit l sz h)
  | red_get: forall l (h: heap) v,
      h l = Some v ->
      red (GET l, h) (PURE v, h)
  | red_set: forall l v (h: heap),
      h l <> None ->
      red (SET l v, h) (SKIP, hupdate l v h)
  | red_free: forall l (h: heap),
      h l <> None ->
      red (FREE l, h) (SKIP, hfree l h).

(** Absence of run-time errors. [immsafe c h] holds if [c / h] is not
    going to abort immediately on a run-time error, such as dereferencing 
    an invalid pointer. *)

Inductive immsafe: com * heap -> Prop :=
  | immsafe_pure: forall v h,
      immsafe (PURE v, h)
  | immsafe_let: forall c f h,
      immsafe (c, h) -> immsafe (LET c f, h)
  | immsafe_ifthenelse: forall b c1 c2 h,
      immsafe (IFTHENELSE b c1 c2, h)
  | immsafe_alloc: forall sz (h: heap) l,
      l <> 0 -> (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
      immsafe (ALLOC sz, h)
  | immsafe_get: forall l (h: heap),
      h l <> None -> immsafe (GET l, h)
  | immsafe_set: forall l v (h: heap),
      h l <> None -> immsafe (SET l v, h)
  | immsafe_free: forall l (h: heap),
      h l <> None -> immsafe (FREE l, h)
  | immsafe_pick: forall n h,
      immsafe (PICK n, h).

(** * 2.  The rules of separation logic *)

Definition precond := assertion.
Definition postcond := Z -> assertion.

(** ** 2.1.  Semantic definition of strong triples *)

(** Instead of axiomatizing the rules of separation logic, then prove
    their soundness against the operational semantics, we define
    triples [ ⦃ P ⦄ c ⦃ Q ⦄ ] directly in terms of the
    operational semantics, then show the rules of separation logic as
    lemmas about these semantic triples.

    Note: the way triples are defined below, they are strong triples
    that guarantee termination.  However, we write them with braces
    instead of brackets, for consistency with the third lecture
    and with the literature on separation logic.
 *)

(** [safe c h Q] holds if [c] started in [h] always terminates without errors,
    and when it terminates with value [v], the postcondition [Q v] holds
    of the final heap. *)

Inductive safe: com -> heap -> postcond -> Prop :=
  | safe_done: forall v h (Q: postcond),
      Q v h ->
      safe (PURE v) h Q
  | safe_step: forall c h Q,
      match c with PURE _ => False | _ => True end ->
      immsafe (c, h) ->
      (forall c' h', red (c, h) (c', h') -> safe c' h' Q) ->
      safe c h Q.

(** We could try to define semantic triples like we did for Hoare logic:
<<
    Definition triple (P: precond) (c: com) (Q: postcond) :=
     forall h, P h -> safe c h Q.
>>
    However, this definition does not validate the frame rule.
    There are reductions, namely [ALLOC sz / h --> PURE l / h'],
    that we can do from a "small" heap [h] but can no longer do from a
    larger heap [hunion h hf] obtained by framing.
    (This happens if the location [l] is fresh in [h] but not in [hf].). *)

(** Instead, we define our separation triples [ ⦃ P ⦄ c ⦃ Q ⦄ ]
    as Hoare triples plus framing: *)

Definition Hoare (P: precond) (c: com) (Q: postcond) : Prop :=
  forall h, P h -> safe c h Q.

Definition triple (P: precond) (c: com) (Q: postcond) :=
  forall (R: assertion), Hoare (P ** R) c (fun v => Q v ** R).

Notation "⦃ P ⦄ c ⦃ Q ⦄" := (triple P c Q) (at level 90, c at next level).

(** This definition validates the frame rule. *)

Lemma triple_frame: forall P c Q R,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄.
Proof.
  intros P c Q R TR R'. rewrite sepconj_assoc.
  replace (fun v => (Q v ** R) ** R') with (fun v => Q v ** (R ** R')).
  apply TR.
  apply functional_extensionality; intros. rewrite sepconj_assoc; auto.
Qed.

Ltac inv H := inversion H; clear H; subst.

(** ** 2.2. The "small rules" for heap operations *)

Lemma triple_get: forall l v,
  ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof.
  intros l v R h (h1 & h2 & H1 & H2 & D & U).
  assert (L1: h1 l = Some v).
  { red in H1. subst h1. apply hupdate_same. }
  assert (L: h l = Some v).
  { intros. rewrite U; simpl. rewrite L1; auto. } 
  constructor; auto.
  - constructor. congruence.
  - intros c' h' RED. inv RED. constructor. 
    exists h1, h2. unfold pureconj. intuition congruence.
Qed.

Lemma triple_set: forall l v,
  ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄.
Proof.
  intros l v R h (h1 & h2 & H1 & H2 & D & U).
  destruct H1 as (v0 & H1). red in H1.
  assert (L1: h1 l = Some v0).
  { subst h1; apply hupdate_same. }
  assert (L: h l = Some v0).
  { rewrite U; cbn. rewrite L1; auto. } 
  constructor; auto.
  - constructor. congruence.
  - intros c' h' RED. inv RED. constructor. 
    exists (hupdate l v hempty), h2.
    split. red. auto.
    split. auto.
    split. intro l'. specialize (D l'). cbn in *. destruct D; auto. destruct (Z.eq_dec l l'); auto. congruence.
    apply heap_extensionality; intros l'; cbn. destruct (Z.eq_dec l l'); auto.
Qed.

Fixpoint valid_N (l: addr) (sz: nat) : assertion :=
  match sz with O => emp | S sz => valid l ** valid_N (l + 1) sz end.

Remark valid_N_init:
  forall (R: assertion) sz l h,
  R h ->
  (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
  (valid_N l sz ** R) (hinit l sz h).
Proof.
  induction sz as [ | sz]; intros l h Rh EMPTY; cbn.
- rewrite sepconj_emp. auto.
- rewrite sepconj_assoc. exists (hupdate l 0 hempty), (hinit (l + 1) sz h).
  split. exists 0. red; auto.
  split. apply IHsz. auto. intros. apply EMPTY. lia.
  split. intros x. unfold hupdate, hempty; cbn. destruct (Z.eq_dec l x); auto.
  right. rewrite hinit_outside by lia. apply EMPTY; lia.
  apply heap_extensionality; intros x. cbn. destruct (Z.eq_dec l x); auto.
Qed. 

Lemma triple_alloc: forall sz,
  ⦃ emp ⦄
  ALLOC sz
  ⦃ fun l => (l <> 0) //\\ valid_N l sz ⦄.
Proof.
  intros sz R h H. rewrite sepconj_emp in H.
  constructor; auto.
- destruct (isfinite h) as (l0 & FIN). apply immsafe_alloc with (Z.max l0 1); intros.
  + lia.
  + apply FIN. lia.
- intros c' h' RED; inv RED. constructor.
  rewrite lift_simple_conj; split. auto. apply valid_N_init; auto.
Qed. 

Lemma triple_free: forall l,
  ⦃ valid l ⦄
  FREE l
  ⦃ fun _ => emp ⦄.
Proof.
  intros l R h (h1 & h2 & H1 & H2 & D & U).
  destruct H1 as (v0 & H1).
  assert (L1: h1 l = Some v0).
  { rewrite H1. apply hupdate_same. }
  assert (L: h l = Some v0).
  { rewrite U; cbn. rewrite L1. auto. } 
  constructor; auto.
- constructor. congruence. 
- intros c' h' RED; inv RED. constructor. rewrite sepconj_emp.
  replace (hfree l (hunion h1 h2)) with h2; auto.
  apply heap_extensionality; intros x. generalize (D x); rewrite H1; cbn.
  destruct (Z.eq_dec l x); auto. intuition congruence.
Qed.

(** ** 2.3. Properties of the [safe] predicate *)

Lemma safe_pure: forall v h Q,
  safe (PURE v) h Q -> Q v h.
Proof.
  intros. inv H. 
- auto.
- contradiction.
Qed.

Lemma safe_red: forall c h Q c' h',
  safe  c h Q -> red (c, h) (c', h') -> safe c' h' Q.
Proof.
  intros. inv H.
- inv H0.
- eauto.
Qed.

Lemma safe_immsafe: forall c h Q,
  safe c h Q -> immsafe (c, h).
Proof.
  intros. inv H.
- constructor.
- auto.
Qed.

Lemma safe_let: forall (Q R: postcond) f,
  (forall v h', Q v h' -> safe (f v) h' R) ->
  forall c h,
  safe c h Q ->
  safe (LET c f) h R.
Proof.
  intros Q R f POST. induction 1.
- constructor; auto.
  + constructor. constructor.
  + intros c' h' RED; inv RED. apply POST; auto. inv H1.
- constructor; auto.
  + constructor; auto.
  + intros c' h' RED; inv RED. contradiction. eauto.
Qed.

Lemma safe_consequence: forall (Q Q': postcond),
  (forall v, Q v -->> Q' v) ->
  forall c h, safe c h Q -> safe c h Q'.
Proof.
  intros Q Q' IMP. induction 1.
- apply safe_done. apply IMP. assumption.
- apply safe_step; auto.
Qed.

(** ** 2.4. Rules for control structures *)

(** Proof plan: first show Hoare-style rules for the [Hoare] triple,
    then frame by an arbitrary [R] to obtain the separation triple. *)

Lemma Hoare_pure: forall P v (Q: postcond),
  P -->> Q v ->
  Hoare P (PURE v) Q.
Proof.
  intros; intros h Ph. constructor. apply H; auto.
Qed.

Lemma triple_pure: forall P v (Q: postcond),
  P -->> Q v ->
  ⦃ P ⦄ PURE v ⦃ Q ⦄.
Proof.
  intros; intros R. apply Hoare_pure. apply sepconj_imp_l; auto.
Qed.

Lemma Hoare_let:
  forall c f (P: precond) (Q R: postcond),
  Hoare P c Q ->
  (forall v, Hoare (Q v) (f v) R) ->
  Hoare P (LET c f) R.
Proof.
  intros until R; intros HR1 HR2 h Ph.
  apply safe_let with Q. apply HR2. apply HR1. auto.
Qed.

Lemma triple_let:
  forall c f (P: precond) (Q R: postcond),
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof.
  intros c f P Q R TR1 TR2 R'.
  apply Hoare_let with (fun v => Q v ** R').
  apply TR1.
  intros. apply TR2.
Qed.

Lemma Hoare_ifthenelse: forall b c1 c2 P Q,
  Hoare ((b <> 0) //\\ P) c1 Q ->
  Hoare ((b = 0) //\\ P) c2 Q ->
  Hoare P (IFTHENELSE b c1 c2) Q.
Proof.
  intros until Q; intros HR1 HR2 h Ph. constructor; auto.
- constructor.
- intros c' h' RED; inv RED. destruct (Z.eqb_spec b 0).
  + apply HR2. split; auto.
  + apply HR1. split; auto.
Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  ⦃ (b <> 0) //\\ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ (b = 0) //\\ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
  intros b c1 c2 P Q TR1 TR2 R.
  apply Hoare_ifthenelse; rewrite <- lift_simple_conj; auto.
Qed.

Lemma Hoare_consequence: forall P P' c Q' Q,
  Hoare P' c Q' ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  Hoare P c Q.
Proof.
  intros; red; intros. apply safe_consequence with Q'; auto. 
Qed.

Lemma triple_consequence: forall P P' c Q' Q,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros; red; intros. apply Hoare_consequence with (P' ** R) (fun v => Q' v ** R).
  apply H.
  apply sepconj_imp_l; auto.
  intros; apply sepconj_imp_l; auto.
Qed.

Lemma Hoare_pick: forall P n,
  Hoare P (PICK n) (fun i => (0 <= i < n) //\\ P).
Proof.
  intros P n h Ph. constructor; auto.
- constructor.
- intros c' h' RED; inv RED. constructor. split; auto.
Qed. 

Lemma triple_pick: forall n,
  ⦃ emp ⦄
  PICK n
  ⦃ fun i => pure (0 <= i < n) ⦄.
Proof.
  intros; intros R. rewrite sepconj_emp. eapply Hoare_consequence with (P' := R). apply Hoare_pick.
  red; auto.
  intros; red; intros. rewrite pureconj_sepconj. auto.
Qed.

(** ** 2.5.  Useful derived rules *)

(** The following rules are heavily used in the examples of section 3. *)

Lemma triple_consequence_pre: forall P P' c Q,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P -->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros. apply triple_consequence with P' Q; auto. intros; red; auto.
Qed.

Lemma triple_consequence_post: forall P c Q Q',
  ⦃ P ⦄ c ⦃ Q' ⦄ ->
  (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros. apply triple_consequence with P Q'; auto. red; auto.
Qed.

Lemma triple_lift_pure: forall (P: Prop) P' c Q,
  (P -> ⦃ P' ⦄ c ⦃ Q ⦄) ->
  ⦃ P //\\ P' ⦄ c ⦃ Q ⦄.
Proof.
  intros. intros R h Ph. rewrite lift_simple_conj in Ph. destruct Ph as [P1 P2].
  apply H; auto.
Qed.

Lemma triple_lift_exists: forall (X: Type) (P: X -> assertion) c Q,
  (forall x, ⦃ P x ⦄ c ⦃ Q ⦄) ->
  ⦃ aexists P ⦄ c ⦃ Q ⦄.
Proof.
  intros. intros R h (h1 & h2 & (x & Px1) & R2 & D & U).
  apply (H x R). exists h1, h2; intuition auto.
Qed.

Lemma triple_ifthen: forall b c1 c2 P Q,
  b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
  intros. apply triple_ifthenelse; apply triple_lift_pure; intros.
- auto.
- lia.
Qed.

Lemma triple_ifelse: forall b c1 c2 P Q,
  b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
  intros. apply triple_ifthenelse; apply triple_lift_pure; intros.
- lia.
- auto.
Qed.

Lemma unroll_com: forall c,
  c = match c with
      | PURE x => PURE x
      | LET c f => LET c f
      | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2
      | ALLOC sz => ALLOC sz
      | GET l => GET l
      | SET l v => SET l v
      | FREE l => FREE l
      | PICK n => PICK n
      end.
Proof.
  destruct c; auto.
Qed.

(** * 3. Singly-linked lists *)

(** ** Representation predicate *)

(** Here is a separation logic assertion that describes the in-memory
    representation of a list.
-   [a] is the pointer to the list head (or 0 if the list is empty).
-   [l] is the Coq list of the list elements.
*)

Fixpoint list_at (a: addr) (l: list Z) : assertion :=
  match l with
  | nil => (a = 0) //\\ emp
  | h :: t => (a <> 0) //\\ aexists (fun a' => contains a h ** contains (a + 1) a' ** list_at a' t)
  end.

(** ** The "cons" operation *)

Definition list_cons (n: Z) (a: addr) : com :=
  LET (ALLOC 2) (fun a' => SEQ (SET a' n) (SEQ (SET (a' + 1) a) (PURE a'))).

Lemma list_cons_correct: forall a n l,
    ⦃ list_at a l ⦄
  list_cons n a
    ⦃ fun a' => list_at a' (n :: l) ⦄.
Proof.
  intros. eapply triple_let.
  rewrite <- sepconj_emp at 1. apply triple_frame. apply triple_alloc.
  intros b; simpl. rewrite lift_simple_conj, ! sepconj_assoc, sepconj_emp.
  apply triple_lift_pure; intros H1.
  eapply triple_let. apply triple_frame. apply triple_set. simpl; intros _.
  eapply triple_let. rewrite sepconj_comm, sepconj_assoc.
  apply triple_frame. apply triple_set. simpl; intros _.
  rewrite sepconj_comm, sepconj_assoc, sepconj_comm, sepconj_assoc.
  apply triple_pure. intros h A. split. auto. exists a; auto.
Qed.   

(** ** Computing the length of a list *)

(** Taking advantage of the coinductive nature of type [com],
    we use infinite commands to represent loops and tail-recursive functions. *)

CoFixpoint list_length_rec (a: addr) (len: Z) : com :=
  IFTHENELSE a (LET (GET (a + 1)) (fun t => list_length_rec t (len + 1))) (PURE len).

Definition list_length (a: addr) : com := list_length_rec a 0.

(** Normally we would write
<<
   len = 0;
   while (a != 0) { a = get (a + 1); len = len + 1; }
>>
   With the coinductive definition, we write the equivalent infinite command
<<
   if (a == 0) return 0; else {
     a1 = get (a + 1);
     if (a1 == 0) return 1; else {
       a2 = get (a1 + 1);
       if (a2 == 0) return 2; else ...
>>
*)

Lemma list_length_rec_correct: forall l a len,
    ⦃ list_at a l ⦄
  list_length_rec a len
    ⦃ fun len' => (len' = len + Z.of_nat (List.length l)) //\\ list_at a l ⦄.
Proof.
Local Opaque Z.of_nat.
  induction l as [ | h t]; intros; rewrite (unroll_com (list_length_rec a len)); cbn.
- apply triple_lift_pure; intro H1.
  apply triple_ifelse; auto.
  apply triple_pure. intros h H2. split. lia. split; auto.
- apply triple_lift_pure; intro H1.
  apply triple_lift_exists; intros a'.
  apply triple_ifthen; auto.
  eapply triple_let.
  rewrite sepconj_comm, sepconj_assoc. 
  apply triple_frame. apply triple_get. simpl.
  intros a''. rewrite lift_simple_conj. apply triple_lift_pure; intros H3. subst a''.
  rewrite sepconj_comm, sepconj_assoc.
  eapply triple_consequence_post.
  apply triple_frame. apply IHt. intros len'; simpl.
  rewrite lift_simple_conj.
  rewrite sepconj_comm. rewrite sepconj_assoc. 
  intros h1 (A & B). split. lia. split. auto. exists a'; auto.
Qed.

Corollary list_length_correct: forall l a,
    ⦃ list_at a l ⦄
  list_length a
    ⦃ fun len => (len = Z.of_nat (length l)) //\\ list_at a l ⦄.
Proof.
  intros. apply list_length_rec_correct.
Qed.

(** ** Concatenating two lists in-place *)

(** In loop notation:
<<
  if (l1 == 0) return l2; else {
    t = get(l1 + 1);
    while (get (t + 1) != 0) t = get (t + 1);
    set (t + 1, l2);
    return l1;
  }
>>
*)

CoFixpoint list_concat_rec (a1 a2: addr) : com :=
  LET (GET (a1 + 1)) (fun t => IFTHENELSE t (list_concat_rec t a2) (SET (a1 + 1) a2)).

Definition list_concat (a1 a2: addr) : com :=
  IFTHENELSE a1 (SEQ (list_concat_rec a1 a2) (PURE a1)) (PURE a2).

Lemma list_concat_rec_correct: forall l2 a2 l1 a1,
  a1 <> 0 ->
    ⦃ list_at a1 l1 ** list_at a2 l2 ⦄
  list_concat_rec a1 a2
    ⦃ fun _ => list_at a1 (l1 ++ l2) ⦄.
Proof.
  induction l1 as [ | h1 t1]; intros; rewrite (unroll_com (list_concat_rec a1 a2)); simpl.
- rewrite lift_simple_conj. apply triple_lift_pure; intros. lia.
- rewrite lift_simple_conj. apply triple_lift_pure. intros H1.
  rewrite lift_aexists. apply triple_lift_exists. intros a'.
  rewrite sepconj_assoc.
  eapply triple_let.
  + rewrite sepconj_comm, ! sepconj_assoc. apply triple_frame. apply triple_get.
  + intros t. simpl. 
    rewrite lift_simple_conj. apply triple_lift_pure. intros H2; subst t.
    apply triple_ifthenelse.
    * apply triple_lift_pure. intros H2. 
      rewrite sepconj_comm, ! sepconj_assoc. rewrite <- sepconj_assoc. 
      eapply triple_consequence_post. apply triple_frame. apply IHt1. auto.
      simpl. intros _. rewrite sepconj_comm, sepconj_assoc.
      intros h P. split; auto. exists a'; auto.
    * apply triple_lift_pure. intros H2.
      eapply triple_consequence_post.
      apply triple_frame.
      eapply triple_consequence_pre. apply triple_set.
      intros h P; exists a'; auto.
      simpl. intros _.
      rewrite <- sepconj_assoc. rewrite <- (sepconj_comm (list_at a' t1)). rewrite sepconj_assoc.
      destruct t1; simpl.
      ** rewrite lift_simple_conj, sepconj_emp.
         rewrite <- (sepconj_comm (contains a1 h1)).
         rewrite <- sepconj_assoc.
         rewrite <- (sepconj_comm (contains a1 h1)).
         rewrite sepconj_assoc.
         intros h (A & B). split; auto. exists a2; auto.
      ** rewrite lift_simple_conj. intros h (A & B). lia.
Qed.

Lemma list_concat_correct: forall l1 a1 l2 a2,
    ⦃ list_at a1 l1 ** list_at a2 l2 ⦄
  list_concat a1 a2
    ⦃ fun a => list_at a (l1 ++ l2) ⦄.
Proof.
  intros. unfold list_concat. apply triple_ifthenelse.
- apply triple_lift_pure; intros H1. 
  eapply triple_let. apply list_concat_rec_correct; auto.
  simpl. intros _. apply triple_pure. red; auto.
- apply triple_lift_pure; intros H1.
  destruct l1; simpl.
  + apply triple_pure. rewrite lift_simple_conj, sepconj_emp. intros h (A & B); auto.
  + rewrite lift_simple_conj. apply triple_lift_pure. intros; lia.
Qed.

(** ** List reversal in place *)

(** In loop notation:
<<
  p = 0;
  while (l != 0) {
    n = get (l + 1);
    set (l + 1, p);
    p = l;
    l = n;
  }
  return p;
>>
*)

CoFixpoint list_rev_rec (a p: addr) : com :=
  IFTHENELSE a
    (LET (GET (a + 1)) (fun n =>
     SEQ (SET (a + 1) p)
         (list_rev_rec n a)))
    (PURE p).

Definition list_rev (a: addr) : com := list_rev_rec a 0.

Lemma list_rev_rec_correct: forall l a l' p,
    ⦃ list_at a l ** list_at p l' ⦄
  list_rev_rec a p
    ⦃ fun x => list_at x (List.rev_append l l') ⦄.
Proof.
  induction l as [ | hd l]; intros; rewrite (unroll_com (list_rev_rec a p)); simpl.
- rewrite lift_simple_conj, sepconj_emp. apply triple_lift_pure; intros H1.
  apply triple_ifelse; auto. apply triple_pure. red; auto.
- rewrite lift_simple_conj; apply triple_lift_pure; intros H1.
  rewrite lift_aexists; apply triple_lift_exists; intros a'.
  apply triple_ifthen; auto.
  eapply triple_let.
  rewrite ! sepconj_assoc, <- sepconj_assoc, (sepconj_comm (contains a hd)), sepconj_assoc.
  apply triple_frame. apply triple_get. intros a''. simpl.
  rewrite lift_simple_conj. apply triple_lift_pure. intros H3. subst a''.
  eapply triple_let.
  apply triple_frame. eapply triple_consequence_pre. 
  apply triple_set. 
  intros h P; exists a'; auto.
  simpl. intros _.
  rewrite <- sepconj_assoc. rewrite (sepconj_comm (contains (a + 1) p)).
  rewrite (sepconj_comm (list_at a' l)). rewrite <- sepconj_assoc. 
  rewrite sepconj_comm. rewrite sepconj_assoc. 
  eapply triple_consequence_pre.
  apply IHl.
  simpl. apply sepconj_imp_r. intros h A. split; auto. exists p; auto.
Qed.

Lemma list_rev_correct: forall a l,
    ⦃ list_at a l ⦄
  list_rev a
    ⦃ fun x => list_at x (List.rev l) ⦄.
Proof.
  intros. rewrite List.rev_alt.
  eapply triple_consequence_pre. apply list_rev_rec_correct. 
  simpl. rewrite sepconj_comm, lift_simple_conj, sepconj_emp.
  intros h A; split; auto.
Qed.
