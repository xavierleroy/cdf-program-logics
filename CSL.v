(** Concurrent separation logic. *)

From Coq Require Import ZArith Lia Bool String List.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Sequences Separation.

Local Open Scope Z_scope.

(** * 1. A language with pointers and concurrency *)

(** Here is a variant of the PTR language (from the course on separation logic)
    with concurrency (the PAR and ATOMIC constructs).

    Like PTR, it's an ML-like language with immutable variables and
    references to mutable memory locations, represented using higher-order
    abstract syntax. *)

Inductive com: Type :=
  | PURE (x: Z)                      (**r command without effects *)
  | LET (c: com) (f: Z -> com)       (**r sequencing of commands *)
  | IFTHENELSE (b: Z) (c1 c2: com    (**r conditional *))
  | REPEAT (c: com)                  (**r iterate [c] until it returns not 0 *)
  | PAR (c1 c2: com)                 (**r run [c1] and [c2] in parallel *)
  | ATOMIC (c: com)                  (**r run [c] as one atomic step *)
  | ALLOC (sz: nat)                  (**r allocate [sz] words of storage *)
  | GET (l: Z)                       (**r dereference a pointer *)
  | SET (l: Z) (v: Z)                (**r assign through a pointer *)
  | FREE (l: Z).                     (**r free one word of storage *)

(** Some derived forms. *)

Definition SKIP: com := PURE 0.

Definition SEQ (c1 c2: com) := LET c1 (fun _ => c2).

(** Locations that can be read / written right now. *)

Fixpoint immacc (l: addr) (c: com) : Prop :=
  match c with
  | LET c _ => immacc l c
  | PAR c1 c2 => immacc l c1 \/ immacc l c2
  | GET l' => l = l'
  | SET l' _ => l = l'
  | FREE l' => l = l'
  | _ => False
  end.

(** Reduction semantics. *)

Inductive red: com * heap -> com * heap -> Prop :=
  | red_let_done: forall x f h,
      red (LET (PURE x) f, h) (f x, h)
  | red_let_step: forall c f h c' h',
      red (c, h) (c', h') ->
      red (LET c f, h) (LET c' f, h')
  | red_ifthenelse: forall b c1 c2 h,
      red (IFTHENELSE b c1 c2, h) ((if Z.eqb b 0 then c2 else c1), h)
  | red_repeat: forall c h,
      red (REPEAT c, h) (LET c (fun b => IFTHENELSE b (PURE b) (REPEAT c)), h)
  | red_par_done: forall v1 v2 h,
      red (PAR (PURE v1) (PURE v2), h) (SKIP, h)
  | red_par_left: forall c1 c2 h c1' h',
      red (c1, h) (c1', h') ->
      red (PAR c1 c2, h) (PAR c1' c2, h')
  | red_par_right: forall c1 c2 h c2' h',
      red (c2, h) (c2', h') ->
      red (PAR c1 c2, h) (PAR c1 c2', h')
  | red_atomic: forall c h v h',
      star red (c, h) (PURE v, h') ->
      red  (ATOMIC c, h) (PURE v, h')
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

(** Run-time errors. This includes race conditions, where a location is
    immediately accessed by two commands running in parallel. *)

Inductive erroneous: com * heap -> Prop :=
  | erroneous_let: forall c f h,
      erroneous (c, h) -> erroneous (LET c f, h)
  | erroneous_par_race: forall c1 c2 h l,
      immacc l c1 /\ immacc l c2 ->
      erroneous (PAR c1 c2, h)
  | erroneous_par_l: forall c1 c2 h,
      erroneous (c1, h) -> erroneous (PAR c1 c2, h)
  | erroneous_par_r: forall c1 c2 h,
      erroneous (c2, h) -> erroneous (PAR c1 c2, h)
  | erroneous_atomic: forall c h c' h',
      star red (c, h) (c', h') ->
      erroneous (c', h') ->
      erroneous (ATOMIC c, h)
  | erroneous_get: forall l (h: heap),
      h l = None -> erroneous (GET l, h)
  | erroneous_set: forall l v (h: heap),
      h l = None -> erroneous (SET l v, h)
  | erroneous_free: forall l (h: heap),
      h l = None -> erroneous (FREE l, h).

(** * 2.  The rules of concurrent separation logic *)

Definition invariant := assertion.
Definition precond := assertion.
Definition postcond := Z -> assertion.

(** ** 2.1.  Semantic definition of weak triples *)

(** We now define "triples" (actually, quadruples) [ J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ ],
  where [c] is a command, [P] a precondition (on the initial memory heap),
  [Q] a postcondition (on the return value and the final memory heap),
  and [J] an invariant about the shared heap that is accessed by atomic
  commands.  This is a weak triple: termination is not guaranteed.

  As in the [Seplog] module, we define the "triple" semantically
  in terms of a [safe n c h1 Q J] predicate over the possible reductions
  of command [c] in heap [h1].

  The definition of [safe] follows Vafeiadis (2011) and uses quantification
  over all possible shared heaps [hj] and framing heaps [hf].

  Step-indexing (the [n] parameter) provides an induction principle
  over the [safe] predicate. *)

Inductive safe: nat -> com -> heap -> postcond -> invariant -> Prop :=
  | safe_zero: forall c h Q J,
      safe O c h Q J
  | safe_done: forall n v h (Q: postcond) (J: invariant),
      Q v h ->
      safe (S n) (PURE v) h Q J
  | safe_step: forall n c (h1: heap) (Q: postcond) (J: invariant)
      (NOTDONE: match c with PURE _ => False | _ => True end)
      (ACC: forall l, immacc l c -> h1 l <> None)
      (IMM: forall hf hj h,
         hdisj3 h1 hj hf ->
         h = hunion h1 (hunion hj hf) ->
         J hj ->
         ~ erroneous (c, h))
      (STEP: forall hf hj h c' h',
         hdisj3 h1 hj hf ->
         h = hunion h1 (hunion hj hf) ->
         J hj ->
         red (c, h) (c', h') ->
         exists h1' hj',
           hdisj3 h1' hj' hf /\
           h' = hunion h1' (hunion hj' hf) /\
           J hj' /\ safe n c' h1' Q J),
      safe (S n) c h1 Q J.

Definition triple (J: invariant) (P: precond) (c: com) (Q: postcond) :=
  forall n h, P h -> safe n c h Q J.

Notation "J '⊢' ⦃ P ⦄ c ⦃ Q ⦄" := (triple J P c Q) (at level 90, c at next level).

(** ** 2.2. Properties about [safe] *)

Ltac inv H := inversion H; clear H; subst.

Lemma safe_pure: forall n v h (Q: postcond) J,
  Q v h -> safe n (PURE v) h Q J.
Proof.
  intros. destruct n; constructor; auto.
Qed.

Lemma safe_pure_inv: forall n v h Q J,
  safe (S n) (PURE v) h Q J -> Q v h.
Proof.
  intros. inv H. auto. contradiction.
Qed.

Lemma safe_red: forall n c h1 Q J hj hf c' h',
  red (c, hunion h1 (hunion hj hf)) (c', h') ->
  safe (S n) c h1 Q J ->
  J hj ->
  hdisj3 h1 hj hf ->
  exists h1' hj',
    hdisj3 h1' hj' hf /\
    h' = hunion h1' (hunion hj' hf) /\
    J hj' /\ safe n c' h1' Q J.
Proof.
  intros. inv H0.
- inv H.
- eauto.
Qed.

Lemma safe_redN: forall n c h1 Q J hj hf c' h',
  starN red n (c, hunion h1 (hunion hj hf)) (c', h') ->
  safe (S n) c h1 Q J ->
  J hj ->
  hdisj3 h1 hj hf ->
  exists h1' hj',
    hdisj3 h1' hj' hf /\
    h' = hunion h1' (hunion hj' hf) /\
    J hj' /\ safe 1%nat c' h1' Q J.
Proof.
  induction n; intros.
- inv H. exists h1, hj; auto.
- inv H. rename c' into c''. rename h' into h''. destruct b as [c' h'].
  edestruct safe_red as (h1' & hj' & A & B & C & D).
  eassumption. eassumption. assumption. assumption.
  subst h'. eapply IHn; eauto.
Qed.

Lemma safe_not_erroneous: forall n c h1 Q J hj hf,
  safe (S n) c h1 Q J ->
  hdisj3 h1 hj hf ->
  J hj ->
  ~ erroneous (c, hunion h1 (hunion hj hf)).
Proof.
  intros. inv H.
- intros ST; inv ST.
- eauto.
Qed.

Lemma safe_immacc: forall n c h1 Q J l,
  safe (S n) c h1 Q J ->
  immacc l c ->
  h1 l <> None.
Proof.
  intros. inv H.
- contradiction.
- eapply ACC; auto.
Qed.

Lemma safe_mono: forall n c h Q J,
  safe n c h Q J -> forall n', (n' <= n)%nat -> safe n' c h Q J.
Proof.
  induction n; intros.
- replace n' with O by lia. constructor.
- destruct n' as [ | n']. constructor. inv H.
  + constructor; auto.
  + constructor; auto; intros.
    edestruct STEP as (h1' & hj' & A & B & C & D); eauto.
    exists h1', hj'; intuition auto.
    apply IHn; auto. lia.
Qed.

(** ** 2.3. The rules of concurrent separation logic *)

(** *** The frame rule *)

Lemma safe_frame:
  forall (R: assertion) (Q: postcond) J n c h h',
  safe n c h Q J -> hdisjoint h h' -> R h' ->
  safe n c (hunion h h') (fun v => Q v ** R) J.
Proof.
  induction n; intros.
- constructor.
- inv H.
  + constructor. exists h, h'; auto.
  + constructor; auto.
  * intros. apply ACC in H. cbn. destruct (h l); congruence.
  * intros. subst h0.
    apply (IMM (hunion h' hf) hj).
    HDISJ.
    rewrite hunion_assoc. f_equal.
    rewrite hunion_comm by HDISJ. rewrite hunion_assoc. f_equal.
    apply hunion_comm. HDISJ.
    auto.
  * intros. subst h0. 
    edestruct (STEP (hunion h' hf) hj) as (h1' & hj' & A & B & C & D).
    4: eauto. HDISJ. 
    rewrite hunion_assoc. f_equal.
    rewrite hunion_comm by HDISJ. rewrite hunion_assoc. f_equal.
    apply hunion_comm. HDISJ.
    auto.
    subst h'0.
    exists (hunion h1' h'), hj'.
    split. HDISJ.
    split. rewrite hunion_assoc. f_equal.
    rewrite hunion_comm by HDISJ. rewrite hunion_assoc. f_equal.
    apply hunion_comm. HDISJ.
    split. assumption.
    apply IHn; auto. HDISJ.
Qed.

Lemma triple_frame: forall J P c Q R,
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ ->
  J ⊢ ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄.
Proof.
  intros; red; intros. destruct H0 as (h1 & h2 & P1 & R2 & D & U). 
  subst h. apply safe_frame; auto.
Qed.

(** *** The frame rule for invariants *)

Lemma safe_frame_invariant:
  forall Q (J J': invariant) n c h,
  safe n c h Q J -> 
  safe n c h Q (J ** J').
Proof.
  induction n; intros.
- constructor.
- inv H.
  + constructor; auto.
  + constructor; auto.
  * intros. destruct H1 as (hj1 & hj2 & A & B & C & D). subst hj h0.
    apply (IMM (hunion hj2 hf) hj1).
    HDISJ.
    f_equal. rewrite hunion_assoc. auto.
    auto.
  * intros. destruct H1 as (hj1 & hj2 & A & B & C & D). subst hj h0.
    edestruct (STEP (hunion hj2 hf) hj1) as (h1' & hj1' & U & V & X & Y).
    4: eauto. HDISJ.
    f_equal. rewrite hunion_assoc. auto.
    auto.
    subst h'.
    exists h1', (hunion hj1' hj2).
    split. HDISJ.
    split. f_equal. rewrite hunion_assoc. auto.
    split. exists hj1', hj2; intuition auto. HDISJ.
    apply IHn; auto.
Qed.

Lemma triple_frame_invariant: forall J J' P c Q,
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ ->
  J ** J' ⊢ ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros; red; intros. apply safe_frame_invariant; auto.
Qed.

(** *** Atomic commands *)

Lemma triple_atomic: forall J P c (Q: postcond),
  emp ⊢ ⦃ P ** J ⦄ c ⦃ fun v => Q v ** J ⦄ ->
  J ⊢ ⦃ P ⦄ ATOMIC c ⦃ Q ⦄.
Proof.
  intros until Q; intros TR n h Ph. destruct n; constructor; auto.
- intros. intro ST; inv ST. 
  apply star_starN in H4. destruct H4 as (N & STEPS).
  rewrite <- hunion_assoc in STEPS. rewrite <- (hunion_empty hf) in STEPS.
  edestruct safe_redN as (h1' & hj' & A & B & C & D).
  eexact STEPS.
  apply TR. exists h, hj. intuition auto. HDISJ.
  reflexivity.
  HDISJ.
  eelim safe_not_erroneous. eexact D. eexact A. eauto. subst h'; auto.
- intros. inv H2.
  apply star_starN in H4. destruct H4 as (N & STEPS).
  rewrite <- hunion_assoc in STEPS. rewrite <- (hunion_empty hf) in STEPS.
  edestruct safe_redN as (h1' & hj' & A & B & C & D).
  eexact STEPS.
  apply TR. exists h, hj. intuition auto. HDISJ.
  reflexivity.
  HDISJ.
  subst h'.
  apply safe_pure_inv in D. destruct D as (h1'' & hj'' & U & V & X & Y).
  subst h1'.
  exists h1'', hj''.
  split. HDISJ.
  split. rewrite hunion_assoc. rewrite C. rewrite hunion_empty. auto.
  split. auto. 
  apply safe_pure. auto.
Qed.

(** *** Sequential commands *)

Lemma triple_pure: forall J P Q v,
  aimp P (Q v) ->
  J ⊢ ⦃ P ⦄ PURE v ⦃ Q ⦄.
Proof.
  intros J P Q v IMP n h Ph. apply safe_pure; auto.
Qed.

Lemma safe_let:
  forall (Q R: postcond) (J: invariant) f n c h,
  safe n c h Q J ->
  (forall v n' h', Q v h' -> (n' < n)%nat -> safe n' (f v) h' R J) ->
  safe n (LET c f) h R J.
Proof.
  induction n; intros until h; intros S1 S2.
- constructor.
- constructor; auto; intros.
  + eapply safe_immacc; eauto. 
  + red; intros. inv H2. eelim safe_not_erroneous; eauto.
  + subst h0. inv H2.
    * exists h, hj; intuition auto. apply S2. eapply safe_pure_inv; eauto. lia.
    * edestruct safe_red as (h1' & hj' & A & B & C & D); eauto.
      exists h1', hj'; intuition auto. 
Qed.

Lemma triple_let:
  forall c f (J: invariant) (P: precond) (Q R: postcond),
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, J ⊢ ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  J ⊢ ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof.
  intros; red; intros. apply safe_let with Q.
  apply H; auto.
  intros; apply H0; auto.
Qed.

Corollary triple_seq:
  forall c1 c2 (J: invariant) (P Q: precond) (R: postcond),
  J ⊢ ⦃ P ⦄ c1 ⦃ fun _ => Q ⦄ ->
  J ⊢ ⦃ Q ⦄ c2 ⦃ R ⦄ ->
  J ⊢ ⦃ P ⦄ SEQ c1 c2 ⦃ R ⦄.
Proof.
  intros. apply triple_let with (fun _ => Q); auto.
Qed.

(** *** Conditionals and loops *)

Lemma safe_ifthenelse:
  forall n b c1 c2 h Q J,
  (b <> 0 -> safe n c1 h Q J) ->
  (b = 0  -> safe n c2 h Q J) ->
  safe (S n) (IFTHENELSE b c1 c2) h Q J.
Proof.
  intros. constructor; auto; intros.
- intro ST; inv ST.
- inv H4. exists h, hj; intuition auto. destruct (Z.eqb_spec b 0); auto.
Qed.

Lemma triple_ifthenelse: forall J b c1 c2 P Q,
  J ⊢ ⦃ (b <> 0) //\\ P ⦄ c1 ⦃ Q ⦄ ->
  J ⊢ ⦃ (b = 0) //\\ P ⦄ c2 ⦃ Q ⦄ ->
  J ⊢ ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
  intros; red; intros.
  destruct n. constructor. apply safe_ifthenelse.
- intros. apply H. split; auto.
- intros. apply H0. split; auto.
Qed.

Lemma triple_repeat: forall J P c Q,
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ ->
  aimp (Q 0) P ->
  J ⊢ ⦃ P ⦄ REPEAT c ⦃ fun v => (v <> 0) //\\ Q v ⦄.
Proof.
  intros J P c Q TR IMP. red; induction n; intros h Ph.
- constructor.
- constructor; auto.
  + intros; intro ST. inv ST.
  + intros. inv H2. exists h, hj; intuition auto.
    apply safe_let with Q.
    * apply TR; auto.
    * intros. destruct n'. constructor. apply safe_ifthenelse.
      ** intros. destruct n'; constructor. split; auto.
      ** intros. apply safe_mono with n. apply IHn. apply IMP. congruence. lia.
Qed.

(** *** Parallel composition *)

Lemma safe_par:
  forall (J: invariant) (Q1 Q2: assertion) n c1 h1 c2 h2,
  safe n c1 h1 (fun _ => Q1) J ->
  safe n c2 h2 (fun _ => Q2) J ->
  hdisjoint h1 h2 ->
  safe n (PAR c1 c2) (hunion h1 h2) (fun _ => Q1 ** Q2) J.
Proof.
  induction n; intros until h2; intros S1 S2 DISJ; constructor; auto.
- cbn; intros. destruct H as [H | H]; eapply safe_immacc in H; eauto.
  destruct (h1 l); congruence.
  destruct (h1 l); congruence.
- intros. intros ST; inv ST.
  + destruct H3 as [IM1 IM2].
    eapply safe_immacc in IM1; eauto.
    eapply safe_immacc in IM2; eauto.
    specialize (DISJ l). tauto.
  + elim (safe_not_erroneous _ _ _ _ _ hj (hunion h2 hf) S1).
    HDISJ.
    auto.
    rewrite hunion_assoc in H3. rewrite <- (hunion_comm hj) by HDISJ.
    rewrite hunion_assoc. rewrite (hunion_comm hj) by HDISJ. assumption.
  + elim (safe_not_erroneous _ _ _ _ _ hj (hunion h1 hf) S2).
    HDISJ.
    auto.
    rewrite <- (hunion_comm h1) in H3 by HDISJ.
    rewrite hunion_assoc in H3. rewrite <- (hunion_comm hj) by HDISJ.
    rewrite hunion_assoc. rewrite (hunion_comm hj) by HDISJ. assumption.
- intros; subst h. inv H2.
  + (* c1 and c2 are PURE *)
    apply safe_pure_inv in S1. apply safe_pure_inv in S2.
    exists (hunion h1 h2), hj; intuition auto.
    apply safe_pure. exists h1, h2; intuition auto.
  + (* c1 reduces *)
    rewrite hunion_assoc in H3. rewrite <- (hunion_comm h2) in H3 by HDISJ.
    rewrite hunion_assoc in H3.
    destruct (safe_red _ _ _ _ _ _ _ _ _ H3 S1) as (h1' & hj' & A & B & C & D).
    auto. HDISJ.
    subst h'.
    exists (hunion h1' h2), hj'.
    split. HDISJ.
    split. rewrite hunion_assoc. f_equal. rewrite <- (hunion_comm h2) by HDISJ. 
    rewrite hunion_assoc. auto.
    split. assumption.
    apply IHn. auto. apply safe_mono with (S n); auto. HDISJ.
  + (* c2 reduces *)
    rewrite <- (hunion_comm h1) in H3 by HDISJ.
    rewrite hunion_assoc in H3. rewrite <- (hunion_comm h1) in H3 by HDISJ.
    rewrite hunion_assoc in H3.
    destruct (safe_red _ _ _ _ _ _ _ _ _ H3 S2) as (h2' & hj' & A & B & C & D).
    auto. HDISJ.
    subst h'.
    exists (hunion h2' h1), hj'.
    split. HDISJ.
    split. rewrite hunion_assoc. f_equal. rewrite <- (hunion_comm h1) by HDISJ.
    rewrite hunion_assoc. auto.
    split. assumption.
    rewrite hunion_comm by HDISJ.
    apply IHn. apply safe_mono with (S n); auto. auto. HDISJ.
Qed.

Lemma triple_par: forall J P1 c1 Q1 P2 c2 Q2,
  J ⊢ ⦃ P1 ⦄ c1 ⦃ fun _ => Q1 ⦄ ->
  J ⊢ ⦃ P2 ⦄ c2 ⦃ fun _ => Q2 ⦄ ->
  J ⊢ ⦃ P1 ** P2 ⦄ PAR c1 c2 ⦃ fun _ => Q1 ** Q2 ⦄.
Proof.
  intros until Q2; intros TR1 TR2 n h Ph.
  destruct Ph as (h1 & h2 & Ph1 & Ph2 & D & U).
  subst h. apply safe_par; auto.
Qed.

(** *** The "small rules" for heap operations *)

Lemma triple_get: forall J l v,
  J ⊢ ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof.
  intros J l v n h Ph.
  assert (L: h l = Some v) by (rewrite Ph; apply hupdate_same).
  destruct n; constructor; auto.
- cbn; intros. congruence.
- intros. subst h0. intro ST; inv ST. cbn in H2. rewrite L in H2. congruence.
- intros. subst h0. inv H2.
  assert (v0 = v). 
  { cbn in H3. rewrite L in H3. congruence. }
  subst v0.
  exists h, hj; intuition auto.
  apply safe_pure. split; auto.
Qed.

Lemma triple_set: forall J l v,
  J ⊢ ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄.
Proof.
  intros J l v n h Ph.
  destruct Ph as (v0 & Ph).
  assert (L: h l = Some v0) by (rewrite Ph; apply hupdate_same).
  destruct n; constructor; auto.
- cbn; intros. congruence.
- intros; intro ST; inv ST. cbn in H3. rewrite L in H3; congruence.
- intros. subst h0. rewrite Ph in H. inv H2.
  exists (hupdate l v hempty), hj; intuition auto.
  + HDISJ. 
    red; intros l0; generalize (H l0); cbn.
    destruct (Z.eq_dec l l0); intuition congruence.
    red; intros l0; generalize (H0 l0); cbn.
    destruct (Z.eq_dec l l0); intuition congruence.
  + rewrite Ph. apply heap_extensionality; intros l0; cbn.
    destruct (Z.eq_dec l l0); auto.
  + apply safe_pure. reflexivity. 
Qed.

Fixpoint valid_N (l: addr) (sz: nat) : assertion :=
  match sz with O => emp | S sz => valid l ** valid_N (l + 1) sz end.

Remark valid_N_init:
  forall sz l,
  (valid_N l sz) (hinit l sz hempty).
Proof.
  induction sz as [ | sz]; intros l; cbn.
- red; auto.
- exists (hupdate l 0 hempty), (hinit (l + 1) sz hempty).
  split. exists 0. red; auto.
  split. apply IHsz.
  split. intros x. unfold hupdate, hempty at 1; cbn.
  destruct (Z.eq_dec l x); auto.
  right. rewrite hinit_outside by lia. auto.
  apply heap_extensionality; intros x. cbn. destruct (Z.eq_dec l x); auto.
Qed. 

Lemma triple_alloc: forall J sz,
  J ⊢ ⦃ emp ⦄  ALLOC sz  ⦃ fun l => valid_N l sz ⦄.
Proof.
  intros J sz n h Ph. red in Ph; subst h.
  destruct n; constructor; auto.
- intros; intro ST. inv ST. 
- intros. rewrite hunion_empty in H0. subst h. inv H2.
  exists (hinit l sz hempty), hj; intuition auto.
  + assert (D: hdisjoint (hinit l sz hempty) (hunion hj hf)).
    { red; intros l0.
      assert (EITHER: l <= l0 < l + Z.of_nat sz \/ l0 < l \/ l + Z.of_nat sz <= l0) by lia.
      destruct EITHER. right; auto. left; apply hinit_outside; auto.
    }
    HDISJ.
  + apply heap_extensionality; intros l0; cbn.
    assert (EITHER: l <= l0 < l + Z.of_nat sz \/ l0 < l \/ l + Z.of_nat sz <= l0) by lia.
    destruct EITHER.
    rewrite ! hinit_inside by auto. auto.
    rewrite ! hinit_outside by auto. auto.
  + apply safe_pure. apply valid_N_init.
Qed.

Lemma triple_free: forall J l,
  J ⊢ ⦃ valid l ⦄ FREE l ⦃ fun _ => emp ⦄.
Proof.
  intros J l n h Ph.
  destruct Ph as (v0 & Ph).
  assert (L: h l = Some v0) by (rewrite Ph; apply hupdate_same).
  destruct n; constructor; auto.
- cbn; intros. congruence.
- intros; intro ST; inv ST. cbn in H3. rewrite L in H3; congruence.
- intros. subst h0. rewrite Ph in H. inv H2.
  exists hempty, hj; intuition auto.
  + HDISJ. 
  + assert (D: hdisjoint (hupdate l v0 hempty) (hunion hj hf)) by HDISJ.
    rewrite Ph. apply heap_extensionality; intros l0; cbn.
    destruct (Z.eq_dec l l0); auto.
    subst l0. destruct (D l); auto. rewrite hupdate_same in H0; congruence.
  + apply safe_pure. reflexivity. 
Qed.

(** *** Structural rules *)

Lemma triple_consequence_pre: forall P' J P c Q,
  J ⊢ ⦃ P' ⦄ c ⦃ Q ⦄ ->
  aimp P P' ->
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros. intros n h Ph. apply H. auto.
Qed.

Lemma safe_consequence:
  forall (Q Q': postcond) (J: invariant),
  (forall v, aimp (Q' v) (Q v)) ->
  forall n c h,
  safe n c h Q' J ->
  safe n c h Q J.
Proof.
  induction n; intros. 
- constructor.
- inv H0.
  + constructor. apply H; auto.
  + constructor; auto.
    intros.
    edestruct STEP as (h1' & hj' & A & B & C & D); eauto.
    exists h1', hj'; intuition auto.
Qed. 

Lemma triple_consequence_post:
  forall Q' J P c Q,
  J ⊢ ⦃ P ⦄ c ⦃ Q' ⦄ ->
  (forall v, aimp (Q' v) (Q v)) ->
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
  intros. intros n h Ph. apply safe_consequence with Q'; auto.
Qed.

Lemma triple_exists_pre: forall J (P: Z -> assertion) c Q,
  (forall v, J ⊢ ⦃ P v ⦄ c ⦃ Q ⦄) ->
  J ⊢ ⦃ aexists P ⦄ c ⦃ Q ⦄.
Proof.
  intros. intros n h Ph. destruct Ph as (v & Ph). apply (H v). auto.
Qed.

Lemma triple_simple_conj_pre: forall J (P1: Prop) P2 c Q,
  (P1 -> J ⊢ ⦃ P2 ⦄ c ⦃ Q ⦄) ->
  J ⊢ ⦃ P1 //\\ P2 ⦄ c ⦃ Q ⦄.
Proof.
  intros. intros n h Ph. destruct Ph. apply H; auto.
Qed.

Lemma triple_or: forall J P c Q P' Q',
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ⊢ ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  J ⊢ ⦃ aor P P' ⦄ c ⦃ fun v => aor (Q v) (Q' v) ⦄.
Proof.
  intros until Q'; intros TR1 TR2 n h [Ph | P'h].
- apply safe_consequence with Q. intros v1 h1; red; auto. apply TR1; auto.
- apply safe_consequence with Q'. intros v1 h1; red; auto. apply TR2; auto.
Qed.

Lemma safe_and: forall J Q Q',
  precise J ->
  forall n c h,
  safe n c h Q J -> safe n c h Q' J -> safe n c h (fun v => aand (Q v) (Q' v)) J.
Proof.
  induction n; intros c h S S'. 
- constructor.
- inv S; inv S'.
+ constructor; split; auto.
+ contradiction.
+ contradiction.
+ constructor; auto.
* intros.
  edestruct STEP as (h1' & hj' & D' & E' & J' & SAFE'); eauto.
  edestruct STEP0 as (h1'' & hj'' & D'' & E'' & J'' & SAFE''); eauto.
  assert (hj' = hj'').
  { apply H with (hunion h1' hf) (hunion h1'' hf); auto.
    HDISJ. HDISJ.
    rewrite ! (hunion_comm hf) by HDISJ.
    rewrite <- ! hunion_assoc.
    rewrite (hunion_comm h1'), (hunion_comm h1'') by HDISJ.
    congruence.
  }
  subst hj''.
  assert (h1' = h1'').
  { apply hunion_invert_l with (hunion hj' hf). congruence. HDISJ. HDISJ. }
  subst h1''.
  exists h1', hj'; auto. 
Qed.

Lemma triple_and: forall J P c Q P' Q',
  precise J ->
  J ⊢ ⦃ P ⦄ c ⦃ Q ⦄ -> J ⊢ ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  J ⊢ ⦃ aand P P' ⦄ c ⦃ fun v => aand (Q v) (Q' v) ⦄.
Proof.
  intros until Q'; intros PR TR1 TR2 n h (Ph & P'h).
  apply safe_and; auto.
Qed.

(** * 3. Mutual exclusion *)

(** ** 3.1.  Spinlocks *)

(** A spinlock is a memory location that contains 0 if it is locked (busy)
    and 1 if it is unlocked (available). *)

Definition lock_invariant (lck: addr) (R: assertion) : assertion :=
  aexists (fun v => contains lck v ** (if Z.eqb v 0 then emp else R)).

(** Locking a spinlock is achieved by atomically setting it to 0 until
    its previous value was not 0. *)

Definition SWAP (l: addr) (new_v: Z) : com :=
  ATOMIC (LET (GET l) (fun old_v => SEQ (SET l new_v) (PURE old_v))).

Definition LOCK (lck: addr) : com :=
  REPEAT (SWAP lck 0).

(** Unlocking a spinlock is achieved by atomically setting it to 1. *)

Definition UNLOCK (lck: addr) : com :=
  ATOMIC (SET lck 1).

Lemma triple_swap:
  forall lck R,
  lock_invariant lck R ⊢ ⦃ emp ⦄ SWAP lck 0 ⦃ fun v => if Z.eqb v 0 then emp else R ⦄.
Proof.
  intros. apply triple_atomic.
  rewrite sepconj_emp. unfold lock_invariant at 1. 
  apply triple_exists_pre; intros v. 
  eapply triple_let with
  (Q := fun v' => ((v' = v) //\\ contains lck v) ** (if v =? 0 then emp else R)).
  apply triple_frame. apply triple_get. 
  cbn. intros v'. rewrite lift_pureconj. apply triple_simple_conj_pre.
  intros EQ; subst v'.
  apply triple_seq with (Q := contains lck 0 ** (if v =? 0 then emp else R)).
  apply triple_frame.
  apply triple_consequence_pre with (valid lck).
  apply triple_set.
  red; intros. exists v; auto.
  apply triple_pure.
  unfold lock_invariant. red; intros. rewrite sepconj_comm, lift_aexists. exists 0.
  rewrite Z.eqb_refl. rewrite <- (sepconj_comm emp), sepconj_emp. assumption.
Qed.

Lemma triple_lock:
  forall lck R,
  lock_invariant lck R ⊢ ⦃ emp ⦄ LOCK lck ⦃ fun _ => R ⦄.
Proof.
  intros. 
  apply triple_consequence_post with (Q' := fun v => (v <> 0) //\\ (if Z.eqb v 0 then emp else R)).
  apply triple_repeat. apply triple_swap.
  rewrite Z.eqb_refl. red; auto.
  intros v h [H1 H2]. apply Z.eqb_neq in H1. rewrite H1 in H2. auto.
Qed.

Lemma triple_unlock:
  forall lck R,
  precise R ->
  lock_invariant lck R ⊢ ⦃ R ⦄ UNLOCK lck ⦃ fun _ => emp ⦄.
Proof.
  intros. apply triple_atomic.
  rewrite sepconj_comm. unfold lock_invariant at 1. rewrite lift_aexists.
  apply triple_exists_pre. intros v. rewrite sepconj_assoc. 
  apply triple_consequence_post with (Q' := fun _ => contains lck 1 ** (if v =? 0 then emp else R) ** R).
  apply triple_frame. 
  apply triple_consequence_pre with (valid lck). apply triple_set.
  red; intros. exists v; auto.
  intros _. intros h P.
  assert ((contains lck 1 ** R) h).
  { eapply sepconj_imp_r; eauto. 
    destruct (v =? 0).
    rewrite sepconj_emp. red; auto.
    apply sepconj_self; auto. }
  rewrite sepconj_emp. exists 1. simpl. auto.
Qed.

(** ** 3.2.  Critical regions *)

(** A critical region is a command that is run in mutual exclusion,
    while holding the associated spinlock. *)

Definition CRITREGION (lck: addr) (c: com) :=
  SEQ (LOCK lck) (LET c (fun v => SEQ (UNLOCK lck) (PURE v))).

Lemma triple_critregion:
  forall lck R c P Q,
  precise R ->
  emp ⊢ ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄ ->
  lock_invariant lck R ⊢ ⦃ P ⦄ CRITREGION lck c ⦃ Q ⦄.
Proof.
  intros.
  apply triple_seq with (Q := R ** P).
  rewrite <- (sepconj_emp P) at 1. apply triple_frame. apply triple_lock.
  eapply triple_let.
  rewrite sepconj_comm. rewrite <- sepconj_emp at 1. apply triple_frame_invariant. apply H0.
  intros. simpl. apply triple_seq with (Q := emp ** Q v).
  rewrite sepconj_comm. apply triple_frame. apply triple_unlock; auto.
  rewrite sepconj_emp. apply triple_pure. red; auto.
Qed.

(** ** 3.3. Conditional critical regions *)

(** A conditional critical region (CCR), as introduced by
    Brinch-Hansen and Hoare, is a command [c] that is run in mutual
    exclusion but only when a condition [b] is true. *)

Definition CCR (lck: addr) (b: com) (c: com) :=
  REPEAT (SEQ (LOCK lck)
              (LET b (fun v => IFTHENELSE v (SEQ c (SEQ (UNLOCK lck) (PURE 1)))
                                            (SEQ (UNLOCK lck) (PURE 0))))).

Lemma triple_ccr:
  forall lck R b c B P Q,
  precise R ->
  emp ⊢ ⦃ P ** R ⦄ b ⦃ fun v => if v =? 0 then P ** R else B ⦄ ->
  emp ⊢ ⦃ B ⦄ c ⦃ fun _ => Q ** R ⦄ ->
  lock_invariant lck R ⊢ ⦃ P ⦄ CCR lck b c ⦃ fun _ => Q ⦄.
Proof.
  intros.
  set (Qloop := fun v => if v =? 0 then P else Q).
  apply triple_consequence_post with (fun v => (v <> 0) //\\ Qloop v).
  2: { intros v h (U & V). red in V. apply Z.eqb_neq in U. rewrite U in V. auto. }
  apply triple_repeat.
  2: { unfold Qloop. intros v U. simpl in U. auto. }
  apply triple_seq with (Q := R ** P).
  { rewrite <- (sepconj_emp P) at 1. apply triple_frame. apply triple_lock. }
  rewrite sepconj_comm at 1.
  eapply triple_let. rewrite <- sepconj_emp at 1. apply triple_frame_invariant. eexact H0.
  intros v. apply triple_ifthenelse.
- (* B succeeded *)
  eapply triple_seq.
  { eapply triple_consequence_pre.
    rewrite <- sepconj_emp at 1. apply triple_frame_invariant. eexact H1.
    intros h (X & Y). apply Z.eqb_neq in X. rewrite X in Y. auto. }
  apply triple_seq with (Q := emp ** Q).
  { rewrite sepconj_comm at 1. apply triple_frame. apply triple_unlock; auto. }
  apply triple_pure. rewrite sepconj_emp. unfold Qloop. cbn. red; auto.
- (* B failed *)
  apply triple_consequence_pre with (P ** R).
  2: { intros h (X & Y). subst v. auto. }
  eapply triple_seq with (Q := emp ** P).
  { rewrite sepconj_comm at 1. apply triple_frame. apply triple_unlock; auto. }
  apply triple_pure.
  rewrite sepconj_emp. unfold Qloop. cbn. red; auto.
Qed.

(** * 4. The producer/consumer problem *)

(** A solution with a one-place buffer and binary semaphores *)

(** We reuse the spinlocks of section 3.1 as binary semaphores. *)

Definition WAIT := LOCK.
Definition POST := UNLOCK.

Definition PRODUCE (buff free busy: addr) (data: Z) : com :=
  SEQ (WAIT free)
      (SEQ (SET buff data)
           (POST busy)).

Definition CONSUME (buff free busy: addr) : com :=
  SEQ (WAIT busy)
      (LET (GET buff) (fun data =>
           (SEQ (POST free) (PURE data)))).

Definition buffer_invariant (R: Z -> assertion) (buff free busy: addr) :=
    lock_invariant free (valid buff)
 ** lock_invariant busy (aexists (fun v => contains buff v ** R v)).

Remark precise_buffer_invariant: forall (R: Z -> assertion) buff,
  (forall v, precise (R v)) ->
  precise (aexists (fun v => contains buff v ** R v)).
Proof.
  intros. apply aexists_precise. apply sepconj_param_precise; auto. apply contains_param_precise.
Qed.

Lemma triple_consume: forall R buff free busy,
  buffer_invariant R buff free busy ⊢
           ⦃ emp ⦄ CONSUME buff free busy ⦃ fun v => R v ⦄.
Proof.
  intros.
  eapply triple_seq.
  unfold buffer_invariant. rewrite sepconj_comm.
  apply triple_frame_invariant.
  apply triple_lock.
  apply triple_exists_pre. intros v.
  eapply triple_let.
  apply triple_frame. apply triple_get.
  intros v'. cbn. rewrite lift_pureconj. apply triple_simple_conj_pre. intros EQ; subst v'.
  apply triple_seq with (emp ** R v).
  unfold buffer_invariant. apply triple_frame_invariant. apply triple_frame.
  eapply triple_consequence_pre. apply triple_unlock. apply valid_precise.
  red; intros; exists v; auto.
  apply triple_pure. rewrite sepconj_emp. red; auto.
Qed.

Lemma triple_produce: forall (R: Z -> assertion) buff free busy data,
  (forall v, precise (R v)) ->
  buffer_invariant R buff free busy ⊢
           ⦃ R data ⦄ PRODUCE buff free busy data ⦃ fun _ => emp ⦄.
Proof.
  intros.
  apply triple_seq with (valid buff ** R data).
  unfold buffer_invariant. apply triple_frame_invariant.
  rewrite <- (sepconj_emp (R data)) at 1.
  apply triple_frame. apply triple_lock.
  apply triple_seq with (contains buff data ** R data).
  apply triple_frame. apply triple_set.
  unfold buffer_invariant. rewrite sepconj_comm. apply triple_frame_invariant.
  eapply triple_consequence_pre.
  apply triple_unlock. apply precise_buffer_invariant. assumption.
  red; intros. exists data; auto.
Qed.
