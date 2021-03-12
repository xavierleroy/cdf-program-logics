(** Heaps and heap assertions for separation logics. *)

From Coq Require Import ZArith Lia Bool String List.
From Coq Require Import FunctionalExtensionality PropExtensionality.

Local Open Scope Z_scope.

(** * 1. Memory heaps *)

(** A memory heap is a partial function from addresses (memory locations) 
    to values, with a finite domain. *)

Definition addr := Z.

Record heap : Type := {
  contents :> addr -> option Z;
  isfinite :  exists i, forall j, i <= j -> contents j = None
}.

Lemma heap_extensionality:
  forall (h1 h2: heap),
  (forall l, h1 l = h2 l) -> h1 = h2.
Proof.
  intros. destruct h1 as [c1 fin1], h2 as [c2 fin2].
  assert (c1 = c2) by (apply functional_extensionality; auto).
  subst c2. f_equal. apply proof_irrelevance.
Qed.

(** The empty heap. *)

Program Definition hempty : heap :=
  {| contents := fun l => None |}.
Next Obligation.
  exists 0; auto.
Qed.

(** The heap that contains [v] at address [l] and is equal to [h] on
    all other addresses. *)

Program Definition hupdate (l: addr) (v: Z) (h: heap) : heap :=
  {| contents := fun l' => if Z.eq_dec l l' then Some v else h l' |}.
Next Obligation.
  destruct (isfinite h) as (i & fin).
  exists (Z.max i (l + 1)); intros.
  destruct (Z.eq_dec l j). lia. apply fin; lia.
Qed.

Lemma hupdate_same: forall l v h, (hupdate l v h) l = Some v.
Proof.
  intros; cbn. destruct (Z.eq_dec l l); congruence.
Qed.

Lemma hupdate_other: forall l v h l', l <> l' -> (hupdate l v h) l' = h l'.
Proof.
  intros; cbn. destruct (Z.eq_dec l l'); congruence.
Qed.

(** The heap [h] after deallocating address [l]. *)

Program Definition hfree (l: addr) (h: heap) : heap :=
  {| contents := fun l' => if Z.eq_dec l l' then None else h l' |}.
Next Obligation.
  destruct (isfinite h) as (i & fin).
  exists i; intros. destruct (Z.eq_dec l j); auto.
Qed.

(** The heap [h] where addresses [l, ..., l + sz - 1] are initialized to 0. *)

Fixpoint hinit (l: addr) (sz: nat) (h: heap) : heap :=
  match sz with O => h | S sz => hupdate l 0 (hinit (l + 1) sz h) end.

Lemma hinit_inside:
  forall h sz l l', l <= l' < l + Z.of_nat sz -> hinit l sz h l' = Some 0.
Proof.
  induction sz; intros; cbn.
- lia.
- destruct (Z.eq_dec l l'); auto. apply IHsz. lia.
Qed.

Lemma hinit_outside:
  forall h sz l l', l' < l \/ l + Z.of_nat sz <= l' -> hinit l sz h l' = h l'.
Proof.
  induction sz; intros; cbn.
- auto.
- destruct (Z.eq_dec l l'). lia. apply IHsz; lia.
Qed.

(** The disjoint union of two heaps. *)

Definition hdisjoint (h1 h2: heap) : Prop :=
  forall l, h1 l = None \/ h2 l = None.

Lemma hdisjoint_sym:
  forall h1 h2, hdisjoint h1 h2 <-> hdisjoint h2 h1.
Proof.
  unfold hdisjoint; intros; split; intros H l; specialize (H l); tauto.
Qed.

Program Definition hunion (h1 h2: heap) : heap :=
  {| contents := fun l => if h1 l then h1 l else h2 l |}.
Next Obligation.
  destruct (isfinite h1) as (i1 & fin1), (isfinite h2) as (i2 & fin2).
  exists (Z.max i1 i2); intros. rewrite fin1, fin2 by lia. auto.
Qed.

Lemma hunion_comm:
  forall h1 h2, hdisjoint h1 h2 -> hunion h2 h1 = hunion h1 h2.
Proof.
  intros; apply heap_extensionality; intros; cbn.
  specialize (H l). destruct (h1 l), (h2 l); intuition congruence.
Qed.

Lemma hunion_assoc:
  forall h1 h2 h3, hunion (hunion h1 h2) h3 = hunion h1 (hunion h2 h3).
Proof.
  intros; apply heap_extensionality; intros; cbn. destruct (h1 l); auto.
Qed.

Lemma hunion_empty:
  forall h, hunion hempty h = h.
Proof.
  intros; apply heap_extensionality; intros; cbn. auto.
Qed.

Lemma hdisjoint_union_l:
  forall h1 h2 h3,
  hdisjoint (hunion h1 h2) h3 <-> hdisjoint h1 h3 /\ hdisjoint h2 h3.
Proof.
  unfold hdisjoint, hunion; cbn; intros. split.
- intros D; split; intros l; destruct (D l); auto; destruct (h1 l); auto.
  discriminate.
- intros [D1 D2] l. destruct (D2 l); auto. destruct (h1 l) eqn:H1; auto. destruct (D1 l); auto. congruence.
Qed.

Lemma hdisjoint_union_r:
  forall h1 h2 h3,
  hdisjoint h1 (hunion h2 h3) <-> hdisjoint h1 h2 /\ hdisjoint h1 h3.
Proof.
  intros. rewrite hdisjoint_sym. rewrite hdisjoint_union_l. 
  rewrite (hdisjoint_sym h2), (hdisjoint_sym h3). tauto.
Qed.

(** Disjointness between three heaps. *)

Definition hdisj3 (h1 h2 h3: heap) :=
  hdisjoint h1 h2 /\ hdisjoint h1 h3 /\ hdisjoint h2 h3.

(** A tactic to prove disjointness statements. *)

Ltac HDISJ :=
  match goal with
  | [ H: hdisj3 _ _ _ |- _ ] =>
      destruct H as (? & ? & ?); HDISJ
  | [ H: hdisjoint (hunion _ _) _ |- _ ] =>
      apply hdisjoint_union_l in H; destruct H; HDISJ
  | [ H: hdisjoint _ (hunion _ _) |- _ ] =>
      apply hdisjoint_union_r in H; destruct H; HDISJ
  | [ |- hdisj3 _ _ _ ] =>
      split; [|split]; HDISJ
  | [ |- hdisjoint (hunion _ _) _ ] =>
      apply hdisjoint_union_l; split; HDISJ
  | [ |- hdisjoint _ (hunion _ _) ] =>
      apply hdisjoint_union_r; split; HDISJ
  | [ |- hdisjoint hempty _ ] =>
      red; auto
  | [ |- hdisjoint _ hempty ] =>
      red; auto
  | [ |- hdisjoint _ _ ] =>
      assumption || (apply hdisjoint_sym; assumption) || idtac
  | _ => idtac
  end.

(** * 2. Assertions for separation logic *)

Definition assertion : Type := heap -> Prop.

(** Implication (entailment). *)

Definition aimp (P Q: assertion) : Prop :=
  forall h, P h -> Q h.

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).

(** Quantification. *)

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun h => exists a: A, P a h.

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun h => forall a: A, P a h.

(** The assertion "the heap is empty". *)

Definition emp : assertion :=
  fun h => h = hempty.

(** The pure assertion: "the heap is empty and P holds". *)

Definition pure (P: Prop) : assertion :=
  fun h => P /\ h = hempty.

(** The assertion "address [l] contains value [v]". 
    The domain of the heap must be the singleton [{l}]. *)

Definition contains (l: addr) (v: Z) : assertion :=
  fun h => h = hupdate l v hempty.

(** The assertion "address [l] is valid" (i.e. in the domain of the heap). *)

Definition valid (l: addr) : assertion := aexists (contains l).

(** The separating conjunction. *)

Definition sepconj (P Q: assertion) : assertion :=
  fun h => exists h1 h2, P h1
                      /\ Q h2
                      /\ hdisjoint h1 h2  /\ h = hunion h1 h2.

Notation "P ** Q" := (sepconj P Q) (at level 60, right associativity).

(** The conjunction of a simple assertion and a general assertion. *)

Definition pureconj (P: Prop) (Q: assertion) : assertion :=
  fun h => P /\ Q h.

Notation "P //\\ Q" := (pureconj P Q) (at level 60, right associativity).

(** Extensional equality between assertions. *)

Lemma assertion_extensionality:
  forall (P Q: assertion),
  (forall h, P h <-> Q h) -> P = Q.
Proof.
  intros. apply functional_extensionality; intros h.
  apply propositional_extensionality. auto.
Qed.

(** ** Properties of separating conjunction *)

Lemma sepconj_comm: forall P Q, P ** Q = Q ** P.
Proof.
  assert (forall P Q h, (P ** Q) h -> (Q ** P) h).
  { intros P Q h (h1 & h2 & P1 & Q2 & EQ & DISJ); subst h.
    exists h2, h1; intuition auto.
    apply hdisjoint_sym; auto.
    symmetry; apply hunion_comm; auto. } 
  intros; apply assertion_extensionality; intros; split; auto.
Qed.

Lemma sepconj_assoc: forall P Q R, (P ** Q) ** R = P ** (Q ** R).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (hx & h3 & (h1 & h2 & P1 & Q2 & EQ & DISJ) & R3 & EQ' & DISJ'). subst hx h.
  rewrite hdisjoint_union_l in EQ'. rewrite hunion_assoc.
  exists h1, (hunion h2 h3); intuition auto.
  exists h2, h3; intuition auto.
  rewrite hdisjoint_union_r; tauto.
- intros (h1 & hx & P1 & (h2 & h3 & Q2 & R3 & EQ & DISJ) & EQ' & DISJ'). subst hx h.
  rewrite hdisjoint_union_r in EQ'. rewrite <- hunion_assoc.
  exists (hunion h1 h2), h3; intuition auto.
  exists h1, h2; intuition auto.
  rewrite hdisjoint_union_l; tauto.
Qed.

Lemma sepconj_emp: forall P, emp ** P = P.
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & EMP1 & P2 & EQ & DISJ). red in EMP1. subst h h1.
  rewrite hunion_empty; auto.
- intros. exists hempty, h; intuition auto. 
  red; auto.
  red; auto.
  rewrite hunion_empty; auto.
Qed.

Lemma sepconj_imp_l: forall P Q R,
  (P -->> Q) -> (P ** R -->> Q ** R).
Proof.
  intros P Q R IMP h (h1 & h2 & P1 & Q2 & D & U).
  exists h1, h2; intuition auto.
Qed.

Lemma sepconj_imp_r: forall P Q R,
  (P -->> Q) -> (R ** P -->> R ** Q).
Proof.
  intros. rewrite ! (sepconj_comm R). apply sepconj_imp_l; auto.
Qed.

(** ** Other useful logical properties *)

Lemma pure_sep: forall P Q,
  pure (P /\ Q) = pure P ** pure Q.
Proof.
  intros. apply assertion_extensionality; intros.
  unfold pure, sepconj. split.
- intros ((A & B) & C). subst h. exists hempty, hempty; intuition auto.
  intro; auto.
  rewrite hunion_empty; auto.
- intros (h1 & h2 & (PP & E1) & (QQ & E2) & C & D).
  subst. rewrite hunion_empty; auto.
Qed.

Lemma pureconj_sepconj: forall P Q,
  pure P ** Q = P //\\ Q.
Proof.
  intros. apply assertion_extensionality; intros.
  unfold pure, sepconj, pureconj; split.
- intros (h1 & h2 & (A & B) & C & D & E).
  split. auto. subst. rewrite hunion_empty. auto.
- intros (A & B). exists hempty, h; intuition auto.  
  intro l. auto.
  rewrite hunion_empty; auto.
Qed.

Lemma lift_pureconj: forall P Q R, (P //\\ Q) ** R = P //\\ (Q ** R).
Proof.
  intros. rewrite <- ! pureconj_sepconj. rewrite sepconj_assoc. auto.
Qed.

Lemma lift_aexists: forall (A: Type) (P: A -> assertion) Q,
  aexists P ** Q = aexists (fun x => P x ** Q).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & (a & P1) & Q2 & DISJ & EQ).
  exists a, h1, h2; auto.
- intros (a & h1 & h2 & P1 & Q2 & DISJ & EQ).
  exists h1, h2; intuition auto. exists a; auto.
Qed.

Lemma sepconj_swap3: forall R P Q, P ** Q ** R = R ** P ** Q.
Proof.
  intros. rewrite <- sepconj_assoc, sepconj_comm. auto.
Qed. 

Lemma sepconj_swap4: forall S P Q R, P ** Q ** R ** S = S ** P ** Q ** R.
Proof.
  intros. rewrite <- sepconj_assoc, sepconj_swap3, sepconj_assoc. auto.
Qed. 

Lemma sepconj_pick2: forall Q P R, P ** Q ** R = Q ** P ** R.
Proof.
  intros. rewrite (sepconj_comm Q), <- sepconj_assoc, sepconj_comm. auto.
Qed. 

Lemma sepconj_pick3: forall R P Q S, P ** Q ** R ** S = R ** P ** Q ** S.
Proof.
  intros. rewrite (sepconj_pick2 R), (sepconj_pick2 P). auto. 
Qed.

(** ** Magic wand *)

Definition wand (P Q: assertion) : assertion :=
  fun h => forall h', hdisjoint h h' -> P h' -> Q (hunion h h').

Notation "P --* Q" := (wand P Q) (at level 70, right associativity).

Lemma wand_intro: forall P Q R,
  P ** Q -->> R  ->  P -->> Q --* R.
Proof.
  intros P Q R IMP h Ph h' DISJ Qh'.
  apply IMP. exists h, h'; auto.
Qed.

Lemma wand_cancel: forall P Q,
  P ** (P --* Q) -->> Q.
Proof.
  intros P Q h (h1 & h2 & Ph1 & Wh2 & D & U). subst h.
  assert (D': hdisjoint h2 h1) by (apply hdisjoint_sym; auto).
  rewrite hunion_comm by auto. apply Wh2; auto.
Qed.

Lemma wand_charact: forall P Q,
  (P --*Q) = (aexists (fun R => (P ** R -->> Q) //\\ R)).
Proof.
  intros P Q; apply assertion_extensionality; intros h; split.
- intros W. exists (P --* Q). split; auto. apply wand_cancel.
- intros (R & A & B) h' D Ph'.
  assert (D': hdisjoint h' h) by (apply hdisjoint_sym; auto).
  rewrite hunion_comm by auto. apply A. exists h', h; auto.
Qed.

Lemma wand_equiv: forall P Q R,
  (P -->> (Q --* R)) <-> (P ** Q -->> R).
Proof.
  intros; split; intros H.
- intros h (h1 & h2 & Ph1 & Wh2 & D & U). subst h.
  apply H; auto.
- apply wand_intro; auto.
Qed.

Lemma wand_imp_l: forall P P' Q,
  (P' -->> P) -> (P --* Q -->> P' --* Q).
Proof.
  intros. intros h W h' DISJ P'h'. apply W; auto.
Qed.

Lemma wand_imp_r: forall P Q Q',
  (Q -->> Q') -> (P --* Q -->> P --* Q').
Proof.
  intros. intros h W h' DISJ Ph'. apply H; apply W; auto.
Qed.

Lemma wand_idem: forall P,
  emp -->> P --* P.
Proof.
  intros P h E. rewrite E. red. intros. rewrite hunion_empty. auto.
Qed.

Lemma wand_pure_l: forall (P: Prop) Q,
  P -> (pure P --* Q) = Q.
Proof.
  intros P Q PP. apply assertion_extensionality. intros h; split.
- intros W. rewrite <- hunion_empty, hunion_comm by HDISJ. apply W. HDISJ. split; auto.
- intros Qh h' DISJ (Ph' & E). subst h'. rewrite hunion_comm, hunion_empty by HDISJ. auto.
Qed.

Lemma wand_curry: forall P Q R,
  (P ** Q --* R) = (P --* Q --* R).
Proof.
  intros; apply assertion_extensionality; intros h; split.
- intros W h1 D1 Ph1 h2 D2 Qh2. rewrite hunion_assoc. apply W. HDISJ. exists h1, h2; intuition auto. HDISJ.
- intros W h' D (h1 & h2 & Ph1 & Qh2 & D12 & U12). subst h'.
  rewrite <- hunion_assoc. apply W. HDISJ. auto. HDISJ. auto.
Qed.

Lemma wand_star: forall P Q R,
  ((P --* Q) ** R ) -->> (P --* (Q ** R)).
Proof.
  intros; intros h (h1 & h2 & W1 & R2 & D & U). subst h. intros h' D' Ph'.
  exists (hunion h1 h'), h2; intuition auto.
  apply W1; auto. HDISJ.
  HDISJ.
  rewrite ! hunion_assoc. f_equal. apply hunion_comm. HDISJ.
Qed.
