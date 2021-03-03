From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Ltac inv H := inversion H; clear H; subst.

(** * 1.  The IMP language *)

(** ** 1.1. Arithmetic expressions *)

Definition ident := string.

(** The abstract syntax: an arithmetic expression is either... *)

Inductive aexp : Type :=
  | CONST (n: Z)                       (**r a constant, or *)
  | VAR (x: ident)                     (**r a variable, or *)
  | PLUS (a1: aexp) (a2: aexp)         (**r a sum of two expressions, or *)
  | MINUS (a1: aexp) (a2: aexp).       (**r a difference of two expressions *)

(** The denotational semantics: an evaluation function that computes
  the integer value denoted by an expression.  This function is
  parameterized by a store [s] that associates values to variables. *)

Definition store : Type := ident -> Z.

Fixpoint aeval (a: aexp) (s: store) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

(** ** 1.2. Boolean expressions *)

(** The IMP language has conditional statements (if/then/else) and
  loops.  They are controlled by expressions that evaluate to Boolean
  values.  Here is the abstract syntax of Boolean expressions. *)

Inductive bexp : Type :=
  | TRUE                              (**r always true *)
  | FALSE                             (**r always false *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r whether [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r whether [a1 <= a2] *)
  | NOT (b1: bexp)                    (**r Boolean negation *)
  | AND (b1: bexp) (b2: bexp).        (**r Boolean conjunction *)

(** Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false]. *)

Fixpoint beval (b: bexp) (s: store) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval a1 s =? aeval a2 s
  | LESSEQUAL a1 a2 => aeval a1 s <=? aeval a2 s
  | NOT b1 => negb (beval b1 s)
  | AND b1 b2 => beval b1 s && beval b2 s
  end.

(** There are many useful derived forms. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** ** 1.3. Commands *)

(** To complete the definition of the IMP language, here is the
  abstract syntax of commands, also known as statements. *)

Inductive com: Type :=
  | SKIP                                     (**r do nothing *)
  | ASSIGN (x: ident) (a: aexp)              (**r assignment: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r sequence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditional: [if b then c1 else c2] *)
  | WHILE (b: bexp) (c1: com)                (**r loop: [while b do c1 done] *)
  | ASSERT (b: bexp)                         (**r assertion (error if false) *)
  | HAVOC (x: ident).                        (**r nondeterministic assignment *)

(** We can write [c1 ;; c2] instead of [SEQ c1 c2], it is easier on the eyes. *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Reduction semantics *)

Definition update (x: ident) (v: Z) (s: store) : store :=
  fun y => if string_dec x y then v else s y.

Lemma update_same: forall x v s, (update x v s) x = v.
Proof.
  unfold update; intros. destruct (string_dec x x); congruence.
Qed.

Lemma update_other: forall x v s y, x <> y -> (update x v s) y = s y.
Proof.
  unfold update; intros. destruct (string_dec x y); congruence.
Qed.

(** The relation [ red (c, s) (c', s') ], written [ c / s --> c' / s' ]
    in the lectures, defines a basic reduction, that is, the first
    computation step when executing command [c] in initial memory
    state [s].
    [s'] is the memory state "after" this computation step.
    [c'] is a command that represent all the computations that remain
    to be performed later.

    The reduction relation is presented as a Coq inductive predicate,
    with one case (one "constructor") for each reduction rule.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval b s then c1 else c2), s)
  | red_while_done: forall b c s,
      beval b s = false ->
      red (WHILE b c, s) (SKIP, s)
  | red_while_loop: forall b c s,
      beval b s = true ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s)
  | red_havoc: forall x s n,
      red (HAVOC x, s) (SKIP, update x n s)
  | red_assert: forall b s,
      beval b s = true ->
      red (ASSERT b, s) (SKIP, s).

(** The predicate [ error c s ] means that command [c] started in state [s]
    causes a run-time error.
    This is written [ c / s --> err ] in the lectures. *)

Fixpoint error (c: com) (s: store) : Prop :=
  match c with
  | ASSERT b => beval b s = false
  | (c1 ;; c2) => error c1 s
  | _ => False
  end.

Definition terminated (c: com) : Prop :=  c = SKIP.

Definition terminates (c: com) (s s': store) : Prop :=
  exists c', star red (c, s) (c', s') /\ terminated c'.

Definition goeswrong (c: com) (s: store) : Prop :=
  exists c' s', star red (c, s) (c', s') /\ error c' s'.

(** * 2.  Hoare logic *)

(** ** 2.1.  Assertions on the values of variables *)

(** Hoare logic manipulates formulas / claims / assertions that "talk about"
    the values of the program variables.  A typical assertion is
    [0 <= x /\ x <= y], meaning "at this program point, the value of 
    variable [x] is positive and less than or equal to the value of
    variable [y]". *)

(** In our Coq development, we represent assertions by Coq logical formulas
    (type [Prop]) parameterized by the current store, which provides
    the values of the variables.
  
    For example, the assertion [0 <= x /\ x <= y] above is represented
    by the Coq predicate [fun s => 0 <= s "x" /\ s "x" <= s "y"]. *)
    
Definition assertion : Type := store -> Prop.

(** Here are some useful assertions.
    Conjunction and disjunction of two assertions. *)

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun s => aeval a s = v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

(** Quantification *)

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => forall (a: A), P a s.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

(** ** 2.2.  The rules of Hoare logic *)

(** Here are the base rules for weak Hoare logic.
    They define a relation [ {{P}} c {{Q}}], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Reserved Notation "{{ P }} c {{ Q }}" (at level 90, c at next level).

Inductive Hoare: assertion -> com -> assertion -> Prop :=
  | Hoare_skip: forall P,
      {{ P }} SKIP {{ P }}
  | Hoare_assign: forall P x a,
      {{ aupdate x a P }} ASSIGN x a {{ P }}
  | Hoare_seq: forall P Q R c1 c2,
      {{ P }} c1 {{ Q }} ->
      {{ Q }} c2 {{ R }} ->
      {{ P }} c1;;c2 {{ R }}
  | Hoare_ifthenelse: forall P Q b c1 c2,
      {{ atrue b //\\ P }} c1 {{ Q }} ->
      {{ afalse b //\\ P }} c2 {{ Q }} ->
      {{ P }} IFTHENELSE b c1 c2 {{ Q }}
  | Hoare_while: forall P b c,
      {{ atrue b //\\ P }} c {{ P }} ->
      {{ P }} WHILE b c {{ afalse b //\\ P }}
  | Hoare_havoc: forall x Q,
      {{ aforall (fun n => aupdate x (CONST n) Q) }} HAVOC x {{ Q }}
  | Hoare_assert: forall P b,
      {{ atrue b //\\ P }} ASSERT b {{ atrue b //\\ P }}
  | Hoare_consequence: forall P Q P' Q' c,
      {{ P }} c {{ Q }} ->
      P' -->> P ->
      Q -->> Q' ->
      {{ P' }} c {{ Q' }}

where "{{ P }} c {{ Q }}" := (Hoare P c Q).

(** Here are the rules for strong Hoare logic, defining strong triples
    [ [[P]] c [[Q]] ].  The only difference with weak triples
    is the rule for while loops. *)

Reserved Notation "[[ P ]] c [[ Q ]]" (at level 90, c at next level).

Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun s => 0 <= aeval a s < v.

Inductive HOARE: assertion -> com -> assertion -> Prop :=
  | HOARE_skip: forall P,
      [[ P ]] SKIP [[ P ]]
  | HOARE_assign: forall P x a,
      [[ aupdate x a P ]] ASSIGN x a [[ P ]]
  | HOARE_seq: forall P Q R c1 c2,
      [[ P ]] c1 [[ Q ]] ->
      [[ Q ]] c2 [[ R ]] ->
      [[ P ]] c1;;c2 [[ R ]]
  | HOARE_ifthenelse: forall P Q b c1 c2,
      [[ atrue b //\\ P ]] c1 [[ Q ]] ->
      [[ afalse b //\\ P ]] c2 [[ Q ]] ->
      [[ P ]] IFTHENELSE b c1 c2 [[ Q ]]
  | HOARE_while: forall P b c a,
      (forall v, 
         [[ atrue b //\\ aequal a v //\\ P ]] c [[ alessthan a v //\\ P ]]) ->
      [[ P ]] WHILE b c [[ afalse b //\\ P ]]
  | HOARE_havoc: forall x Q,
      [[ aforall (fun n => aupdate x (CONST n) Q) ]] HAVOC x [[ Q ]]
  | HOARE_assert: forall P b,
      [[ atrue b //\\ P ]] ASSERT b [[ atrue b //\\ P ]]
  | HOARE_consequence: forall P Q P' Q' c,
      [[ P ]] c [[ Q ]] ->
      P' -->> P ->
      Q -->> Q' ->
      [[ P' ]] c [[ Q' ]]

where "[[ P ]] c [[ Q ]]" := (HOARE P c Q).

(** ** 2.3. Derived and admissible rules *)

Lemma Hoare_consequence_pre: forall P P' Q c,
      {{ P }} c {{ Q }} ->
      P' -->> P ->
      {{ P' }} c {{ Q }}.
Proof.
  intros. apply Hoare_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      {{ P }} c {{ Q }} ->
      Q -->> Q' ->
      {{ P }} c {{ Q' }}.
Proof.
  intros. apply Hoare_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Floyd_assign: forall P x a,
  {{ P }} ASSIGN x a {{ aexists (fun x0 => aexists (fun v =>
                          aequal (VAR x) v //\\
                          aupdate x (CONST x0) (P //\\ aequal a v))) }}.
Proof.
  intros. eapply Hoare_consequence_pre. apply Hoare_assign.
  intros s Ps.
  set (x0 := s x).
  set (v := aeval a s).
  set (s' := update x v s).
  set (s'' := update x x0 s').
  assert (s'' = s).
  { apply functional_extensionality; intros.
    unfold s'', s', update. destruct (string_dec x x1). subst x1; auto. auto. } 
  unfold aupdate. exists x0. exists v.
  split. red; cbn. apply update_same.
  cbn; fold v; fold s'; fold s''. rewrite H. split; auto. red; auto.
Qed.

(** Some derived constructs, with proof rules *)

Lemma Hoare_ifthen: forall b c P Q,
    {{ atrue b //\\ P }} c {{ Q }} ->
    afalse b //\\ P -->> Q ->
    {{ P }} IFTHENELSE b c SKIP {{ Q }}.
Proof.
  intros. apply Hoare_ifthenelse; auto.
  apply Hoare_consequence_pre with Q; auto using Hoare_skip.
Qed.

Definition REPEAT (c: com) (b: bexp) : com :=
  c ;; WHILE b c.

Lemma Hoare_repeat: forall P b c,
  {{ atrue b //\\ P }} c {{ P }} ->
  {{ atrue b //\\ P }} REPEAT c b {{ afalse b //\\ P }}.
Proof.
  intros. apply Hoare_seq with P. auto.
  apply Hoare_while. auto.
Qed.

(** A frame rule for strong triples.  Used to reason about "for" loops below. *)

Fixpoint assigns (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | SEQ c1 c2 => assigns c1 x \/ assigns c2 x
  | IFTHENELSE b c1 c2 => assigns c1 x \/ assigns c2 x
  | WHILE b c => assigns c x
  | ASSERT b => False
  | HAVOC y => x = y
  end.

Definition independent (A: assertion) (vars: ident -> Prop) : Prop :=
  forall (s1 s2: store),
  (forall x, vars x \/ s1 x = s2 x) ->
  A s1 -> A s2.

Ltac Tauto :=
  let s := fresh "s" in
  unfold aand, aor, aimp in *;
  intro s;
  repeat (match goal with [ H: (forall (s': store), _) |- _ ] => specialize (H s) end);
  intuition auto.

Lemma HOARE_frame:
  forall R P c Q,
  [[ P ]] c [[ Q ]] ->
  independent R (assigns c) ->
  [[ P //\\ R ]] c [[ Q //\\ R ]].
Proof.
  intros R.
  assert (IND_SUB: forall (vars1 vars2: ident -> Prop),
                   independent R vars1 -> 
                   (forall x, vars2 x -> vars1 x) ->
                   independent R vars2).
  { unfold independent; intros. apply H with s1; auto. intros. destruct (H1 x); auto. }
  induction 1; intros IND; simpl in IND.
- apply HOARE_skip.
- eapply HOARE_consequence with (Q := P //\\ R).
  apply HOARE_assign.
  unfold aupdate; intros s [A B]. split. auto. apply IND with s; auto.
  intros y. unfold update. destruct (string_dec x y); auto.
  Tauto.
- apply HOARE_seq with (Q //\\ R).
  apply IHHOARE1. eapply IND_SUB; eauto. cbn; intros; tauto.
  apply IHHOARE2. eapply IND_SUB; eauto. cbn; intros; tauto.
- apply HOARE_ifthenelse.
  eapply HOARE_consequence with (Q := Q //\\ R).
  apply IHHOARE1. eapply IND_SUB; eauto. cbn; intros; tauto.
  Tauto. Tauto.
  eapply HOARE_consequence with (Q := Q //\\ R).
  apply IHHOARE2. eapply IND_SUB; eauto. cbn; intros; tauto.
  Tauto. Tauto.
- eapply HOARE_consequence with (P := P //\\ R).
  apply HOARE_while with a. intros.
  eapply HOARE_consequence. apply (H0 v). auto.
  Tauto. Tauto. Tauto. Tauto.
- eapply HOARE_consequence with (Q := Q //\\ R).
  apply HOARE_havoc. 
  intros s [A B] n; split. apply A. apply IND with s; auto. 
  intros y. unfold update. destruct (string_dec x y); auto.
  Tauto.
- eapply HOARE_consequence.
  apply HOARE_assert with (P := P //\\ R). Tauto. Tauto.
- eapply HOARE_consequence. 
  apply IHHOARE; auto.
  intros s [A B]; split; auto.
  intros s [A B]; split; auto.
Qed.

(** A counted "for" loop *)

Definition FOR (i: ident) (l: aexp) (h: ident) (c: com) : com :=
  ASSIGN i l;;
  WHILE (LESSEQUAL (VAR i) (VAR h)) (c ;; ASSIGN i (PLUS (VAR i) (CONST 1))).

Lemma HOARE_for: forall l h i c P,
  [[ atrue (LESSEQUAL (VAR i) (VAR h)) //\\ P ]]
    c
  [[ aupdate i (PLUS (VAR i) (CONST 1)) P ]] ->
  ~assigns c i -> ~assigns c h -> i <> h -> 
  [[ aupdate i l P ]] FOR i l h c [[ afalse (LESSEQUAL (VAR i) (VAR h)) //\\ P ]].
Proof.
  intros. apply HOARE_seq with P. apply HOARE_assign.
  set (variant := PLUS (MINUS (VAR h) (VAR i)) (CONST 1)).
  apply HOARE_while with (a := variant).
  intro v.
  eapply HOARE_seq.
  eapply HOARE_consequence.
  apply HOARE_frame with (R := aequal variant v //\\ atrue (LESSEQUAL (VAR i) (VAR h))).
  eexact H.
  intros s1 s2 E. unfold aequal, atrue, aand; simpl.
  destruct (E i) as [A | A]. contradiction. rewrite A.
  destruct (E h) as [B | B]. contradiction. rewrite B.
  auto.
  Tauto.
  intros s A. eexact A.
  eapply HOARE_consequence with (Q := alessthan variant v //\\ P).
  apply HOARE_assign.
  intros s (A & B & C). unfold aequal in B; simpl in B. unfold atrue in C; simpl in C. apply Z.leb_le in C.
  split. red; simpl. rewrite update_same. rewrite update_other by auto. lia.
  exact A.
  Tauto.
Qed.

(** Some inversion lemmas *)

Lemma Hoare_skip_inv: forall P Q,
  {{ P }} SKIP {{ Q }} -> (P -->> Q).
Proof.
  intros P Q H; dependent induction H.
- red; auto.
- red; intros. apply H1, IHHoare, H0; auto.
Qed.

Lemma Hoare_assign_inv: forall x a P Q,
  {{ P }} ASSIGN x a {{ Q }} -> (P -->> aupdate x a Q).
Proof.
  intros x a P Q H; dependent induction H.
- red; auto.
- red; intros; red. apply H1, IHHoare, H0; auto.
Qed.

Lemma Hoare_seq_inv: forall c1 c2 P Q,
  {{ P }} c1 ;; c2  {{ Q  }} ->
  exists R, {{ P }} c1 {{ R }} /\ {{ R }} c2 {{ Q }}.
Proof.
  intros c1 c2 P Q H; dependent induction H.
- exists Q; auto.
- edestruct IHHoare as (R & C1 & C2); eauto.
  exists R; split; eauto using Hoare_consequence_pre, Hoare_consequence_post.
Qed.

Lemma Hoare_ifthenelse_inv: forall b c1 c2 P Q,
  {{ P }} IFTHENELSE b c1 c2 {{ Q }} ->
  {{ atrue b //\\ P }} c1 {{ Q }} /\ {{ afalse b //\\ P }} c2 {{ Q }}.
Proof.
  intros b c1 c2 P Q H; dependent induction H.
- split; auto.
- edestruct IHHoare as (C1 & C2); eauto.
  split; eapply Hoare_consequence; eauto.
  intros s [A B]; split; auto.
  intros s [A B]; split; auto.
Qed.

Lemma Hoare_while_inv: forall b c P Q,
  {{ P }} WHILE b c {{ Q }} ->
  exists Inv, {{ atrue b //\\ Inv }} c {{ Inv }}
           /\ (P -->> Inv) /\ (afalse b //\\ Inv -->> Q).
Proof.
  intros b c P Q H; dependent induction H.
- exists P; split; auto. split; Tauto.
- edestruct IHHoare as (Inv & C & X & Y); eauto.
  exists Inv; split; auto. split; Tauto.
Qed.

Lemma Hoare_havoc_inv: forall x P Q,
  {{ P }} HAVOC x {{ Q }} -> (P -->> aforall (fun n => aupdate x (CONST n) Q)).
Proof.
  intros x P Q H; dependent induction H.
- red; auto.
- intros s Ps n. apply H1. apply IHHoare; auto. 
Qed.

Lemma Hoare_assert_inv: forall b P Q,
  {{ P }} ASSERT b {{ Q }} ->
  exists R, (P -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q).
Proof.
  intros b P Q H; dependent induction H.
- exists P; split; Tauto.
- edestruct IHHoare as (R & A & B); eauto.
  exists R; split; Tauto.
Qed.

(** Some admissible rules *)

Lemma Hoare_conj:
  forall c P1 P2 Q1 Q2,
  {{ P1 }} c {{ Q1 }} -> {{ P2 }} c {{ Q2 }} ->
  {{ P1 //\\ P2 }} c {{ Q1 //\\ Q2 }}.
Proof.
  induction c; intros.
- apply Hoare_skip_inv in H. apply Hoare_skip_inv in H0.
  eapply Hoare_consequence_post. apply Hoare_skip. Tauto.
- apply Hoare_assign_inv in H. apply Hoare_assign_inv in H0.
  eapply Hoare_consequence_pre. apply Hoare_assign. unfold aupdate in *; Tauto. 
- apply Hoare_seq_inv in H. destruct H as (R1 & C11 & C21).
  apply Hoare_seq_inv in H0. destruct H0 as (R2 & C12 & C22).
  apply Hoare_seq with (R1 //\\ R2); auto.
- apply Hoare_ifthenelse_inv in H. destruct H as (C11 & C21).
  apply Hoare_ifthenelse_inv in H0. destruct H0 as (C12 & C22).
  apply Hoare_ifthenelse.
  eapply Hoare_consequence_pre. eauto. Tauto.
  eapply Hoare_consequence_pre. eauto. Tauto.
- apply Hoare_while_inv in H. destruct H as (Inv1 & C1 & A1 & B1).
  apply Hoare_while_inv in H0. destruct H0 as (Inv2 & C2 & A2 & B2).
  eapply Hoare_consequence with (P := Inv1 //\\ Inv2).
  apply Hoare_while.
  eapply Hoare_consequence_pre. eapply IHc; eauto. Tauto.
  Tauto. Tauto.
- intros. apply Hoare_assert_inv in H. destruct H as (R1 & A1 & B1).
  apply Hoare_assert_inv in H0. destruct H0 as (R2 & A2 & B2).
  eapply Hoare_consequence. eapply Hoare_assert with (P := R1 //\\ R2).
  Tauto. Tauto.
- apply Hoare_havoc_inv in H.
  apply Hoare_havoc_inv in H0.
  eapply Hoare_consequence_pre. apply Hoare_havoc.
  unfold aupdate, aforall in *; Tauto. 
Qed.

Lemma Hoare_disj:
  forall c P1 P2 Q1 Q2,
  {{ P1 }} c {{ Q1 }} -> {{ P2 }} c {{ Q2 }} ->
  {{ P1 \\// P2 }} c {{ Q1 \\// Q2 }}.
Proof.
  induction c; intros.
- apply Hoare_skip_inv in H. apply Hoare_skip_inv in H0.
  eapply Hoare_consequence_post. apply Hoare_skip. Tauto.
- apply Hoare_assign_inv in H. apply Hoare_assign_inv in H0.
  eapply Hoare_consequence_pre. apply Hoare_assign. unfold aupdate in *; Tauto. 
- apply Hoare_seq_inv in H. destruct H as (R1 & C11 & C21).
  apply Hoare_seq_inv in H0. destruct H0 as (R2 & C12 & C22).
  apply Hoare_seq with (R1 \\// R2); auto.
- apply Hoare_ifthenelse_inv in H. destruct H as (C11 & C21).
  apply Hoare_ifthenelse_inv in H0. destruct H0 as (C12 & C22).
  apply Hoare_ifthenelse.
  eapply Hoare_consequence_pre. eauto. Tauto.
  eapply Hoare_consequence_pre. eauto. Tauto.
- apply Hoare_while_inv in H. destruct H as (Inv1 & C1 & A1 & B1).
  apply Hoare_while_inv in H0. destruct H0 as (Inv2 & C2 & A2 & B2).
  eapply Hoare_consequence with (P := Inv1 \\// Inv2).
  apply Hoare_while.
  eapply Hoare_consequence_pre. eapply IHc; eauto. Tauto.
  Tauto. Tauto.
- intros. apply Hoare_assert_inv in H. destruct H as (R1 & A1 & B1).
  apply Hoare_assert_inv in H0. destruct H0 as (R2 & A2 & B2).
  eapply Hoare_consequence. eapply Hoare_assert with (P := R1 \\// R2).
  Tauto. Tauto.
- apply Hoare_havoc_inv in H.
  apply Hoare_havoc_inv in H0.
  eapply Hoare_consequence_pre. apply Hoare_havoc.
  unfold aupdate, aforall in *; Tauto. 
Qed.

Definition choice_axiom :=
  forall (A B: Type) (R: A -> B -> Prop),
  (forall a, exists b, R a b) ->
  exists f: A -> B, forall a, R a (f a).

Lemma Hoare_exists:
  choice_axiom ->
  forall (X: Type) c (P Q: X -> assertion),
  (forall x, {{ P x }} c {{ Q x }}) ->
  {{ aexists P }} c {{ aexists Q }}.
Proof.
  intros CHOICE X. induction c; intros P Q H.
- assert (H': forall x, P x -->> Q x) by (intros; apply Hoare_skip_inv; auto).
  eapply Hoare_consequence_pre. apply Hoare_skip. 
  intros s (x & Px). exists x; apply H'; auto.
- assert (H': forall y, P y -->> aupdate x a (Q y)).
  { intros. apply Hoare_assign_inv. auto. }
  eapply Hoare_consequence_pre. apply Hoare_assign.
  intros s (y & Py). exists y. apply H'; auto.
- set (REL := fun (x : X) (R: assertion) => Hoare (P x) c1 R /\ Hoare R c2 (Q x)).
  assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
  { apply CHOICE. intros x. apply Hoare_seq_inv. auto. }
  destruct H' as (R & H').
  apply Hoare_seq with (aexists R).
  apply IHc1. intros; apply H'.
  apply IHc2. intros; apply H'.
- assert (H1: Hoare (aexists (fun x => atrue b //\\ P x)) c1 (aexists Q)).
  { apply IHc1. intros. specialize (H x). apply Hoare_ifthenelse_inv in H. tauto. }
  assert (H2: Hoare (aexists (fun x => afalse b //\\ P x)) c2 (aexists Q)).
  { apply IHc2. intros. specialize (H x). apply Hoare_ifthenelse_inv in H. tauto. }
  apply Hoare_ifthenelse; eapply Hoare_consequence_pre; eauto.
  intros s (A & x & B). exists x; split; auto.
  intros s (A & x & B). exists x; split; auto.
- set (REL := fun (x : X) (Inv: assertion) =>
          Hoare (atrue b //\\ Inv) c Inv /\ (P x -->> Inv) /\ (afalse b //\\ Inv -->> Q x)).
  assert (H': exists Inv: X -> assertion, forall x: X, REL x (Inv x)).
  { apply CHOICE. intros x. apply Hoare_while_inv. auto. }
  destruct H' as (Inv & H').
  eapply Hoare_consequence with (P := aexists Inv).
  apply Hoare_while.
  apply Hoare_consequence_pre with (P := aexists (fun x => atrue b //\\ Inv x)).
  apply IHc. intros x. apply H'. 
  intros s (A & x & B); exists x; split; auto.
  intros s (x & A). exists x; apply H'; auto.
  intros s (A & x & B); exists x; apply H'; split; auto.
- intros.
  set (REL := fun (x : X) (R: assertion) => 
                (P x -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q x)).
  assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
  { apply CHOICE. intros x. apply Hoare_assert_inv. auto. }
  destruct H' as (R & A).
  eapply Hoare_consequence.
  apply Hoare_assert with (P := aexists R).
  intros s (x & Px). destruct (A x) as (B & C). apply B in Px. destruct Px. split; auto. exists x; auto.
  intros s (Bs & x & Rx). destruct (A x) as (B & C). exists x. apply C. split; auto.
- assert (H': forall y, P y -->> aforall (fun n => aupdate x (CONST n) (Q y))).
  { intros. apply Hoare_havoc_inv. auto. }
  eapply Hoare_consequence_pre. apply Hoare_havoc.
  intros s (y & Py). exists y. apply H'; auto.
Qed.

Lemma Hoare_forall:
  choice_axiom ->
  forall (X: Type) (inhabited: X) c (P Q: X -> assertion),
  (forall x, {{ P x }} c {{ Q x }}) ->
  {{ aforall P }} c {{ aforall Q }}.
Proof.
  intros CHOICE X inhabited; induction c; intros P Q H.
- assert (H': forall x, P x -->> Q x) by (intros; apply Hoare_skip_inv; auto).
  eapply Hoare_consequence_pre. apply Hoare_skip.
  intros s Ps x. apply H'. apply Ps.
- assert (H': forall y, P y -->> aupdate x a (Q y)).
  { intros. apply Hoare_assign_inv. auto. }
  eapply Hoare_consequence_pre. apply Hoare_assign.
  intros s Ps y. apply H'. auto. 
- set (REL := fun (x : X) (R: assertion) => Hoare (P x) c1 R /\ Hoare R c2 (Q x)).
  assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
  { apply CHOICE. intros x. apply Hoare_seq_inv. auto. }
  destruct H' as (R & H').
  apply Hoare_seq with (aforall R).
  apply IHc1. intros; apply H'.
  apply IHc2. intros; apply H'.
- assert (H1: Hoare (aforall (fun x => atrue b //\\ P x)) c1 (aforall Q)).
  { apply IHc1. intros. specialize (H x). apply Hoare_ifthenelse_inv in H. tauto. }
  assert (H2: Hoare (aforall (fun x => afalse b //\\ P x)) c2 (aforall Q)).
  { apply IHc2. intros. specialize (H x). apply Hoare_ifthenelse_inv in H. tauto. }
  apply Hoare_ifthenelse; eapply Hoare_consequence_pre; eauto.
  intros s (A & B) x. split; auto. 
  intros s (A & B) x. split; auto.
- set (REL := fun (x : X) (Inv: assertion) =>
          Hoare (atrue b //\\ Inv) c Inv /\ (P x -->> Inv) /\ (afalse b //\\ Inv -->> Q x)).
  assert (H': exists Inv: X -> assertion, forall x: X, REL x (Inv x)).
  { apply CHOICE. intros x. apply Hoare_while_inv. auto. }
  destruct H' as (Inv & H').
  eapply Hoare_consequence with (P := aforall Inv).
  apply Hoare_while.
  apply Hoare_consequence_pre with (P := aforall (fun x => atrue b //\\ Inv x)).
  apply IHc. intros x. apply H'. 
  intros s [A B] x; split; auto.
  intros s A x. apply H'; auto.
  intros s [A B] x. apply H'; split; auto.
- intros.
  set (REL := fun (x : X) (R: assertion) => 
                (P x -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q x)).
  assert (H': exists R: X -> assertion, forall x: X, REL x (R x)).
  { apply CHOICE. intros x. apply Hoare_assert_inv. auto. }
  destruct H' as (R & A).
  eapply Hoare_consequence.
  apply Hoare_assert with (P := aforall R).
  intros s Pall; split.
  destruct (A inhabited) as (B & C). apply B; auto.
  intros x. destruct (A x) as (B & C). apply B; auto.
  intros s (Bs & Rall) x. destruct (A x) as (B & C). apply C; split; auto.
- assert (H': forall y, P y -->> aforall (fun n => aupdate x (CONST n) (Q y))).
  { intros. apply Hoare_havoc_inv. auto. }
  eapply Hoare_consequence_pre. apply Hoare_havoc.
  intros s Pall n y. apply H'. auto.
Qed.

(** ** 2.4. Soundness *)

(** Soundness of Hoare logic, in the style of type soundness proofs *)

Module Soundness1.

Lemma Hoare_safe:
  forall P c Q,
  {{ P }} c {{ Q }} ->
  forall s, P s -> ~(error c s).
Proof.
  induction 1; intros s Ps; simpl; auto. destruct Ps. red in H. congruence.
Qed.

Lemma Hoare_step:
  forall P c Q,
  {{ P }} c {{ Q }} ->
  forall s c' s',
  P s -> red (c, s) (c', s') -> exists P', {{ P' }} c' {{ Q }} /\ P' s'.
Proof.
  induction 1; intros s c' s' Ps RED.
- inv RED.
- inv RED.
  exists P; split. constructor. exact Ps.
- inv RED.
  + exists Q; split. assumption. eapply Hoare_skip_inv; eauto.
  + destruct (IHHoare1 _ _ _ Ps H2) as (P' & HO' & Ps').
    exists P'; split; auto. apply Hoare_seq with Q; auto.
- inv RED.
  exists (if beval b s' then atrue b //\\ P else afalse b //\\ P); split.
  destruct (beval b s'); auto.
  unfold aand, atrue, afalse. destruct (beval b s') eqn:B; auto.
- inv RED.
  + exists (afalse b //\\ P); split. constructor. unfold aand, afalse; auto.
  + exists (atrue b //\\ P); split.
    apply Hoare_seq with P; auto. apply Hoare_while; auto.
    unfold aand, atrue; auto.
- inv RED. exists Q; split. constructor. apply Ps.
- destruct Ps as [Ps1 Ps2]. inv RED.
  exists (atrue b //\\ P); split. constructor. split; auto.
- apply H0 in Ps. destruct (IHHoare _ _ _ Ps RED) as (R & HO & Rs').
  exists R; split; auto. apply Hoare_consequence_post with Q; auto.
Qed.

Corollary Hoare_steps:
  forall P Q c s c' s',
  {{ P }} c {{ Q }} -> P s -> star red (c, s) (c', s') ->
  exists P', {{ P' }} c' {{ Q }} /\ P' s'.
Proof.
  assert (REC: forall cs cs', star red cs cs' ->
               forall P Q, Hoare P (fst cs) Q -> P (snd cs) ->
               exists P', Hoare P' (fst cs') Q /\ P' (snd cs')).
  { induction 1; intros.
  - exists P; auto.
  - destruct a as [c1 s1], b as [c2 s2], c as [c3 s3]; simpl in *.
    destruct (Hoare_step _ _ _ H1 _ _ _ H2 H) as (R & HO & Rs2).
    eapply IHstar; eauto.
  }
  intros. eapply (REC (c, s) (c', s')); eauto.
Qed.

Corollary Hoare_sound:
  forall P c Q s,
  {{ P }} c {{ Q }} -> P s ->
  ~ goeswrong c s /\ (forall s', terminates c s s' -> Q s').
Proof.
  intros P c Q s HO Ps; split.
- intros (c' & s' & RED & STUCK).
  destruct (Hoare_steps _ _ _ _ _ _ HO Ps RED) as (P' & HO' & Ps').
  eapply Hoare_safe; eauto. 
- intros s' (c' & RED & TERM). red in TERM. subst c'.  
  destruct (Hoare_steps _ _ _ _ _ _ HO Ps RED) as (P' & HO' & Ps').
  eapply Hoare_skip_inv; eauto.
Qed.

End Soundness1.

(** Soundness of strong Hoare logic, using an inductive "safe" predicate *)

Module Soundness2.

Inductive safe (Q: assertion): com -> store -> Prop :=
  | safe_now: forall c s,
      terminated c -> Q s ->
      safe Q c s
  | safe_step: forall c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q c' s') ->
      safe Q c s.

Definition Triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

Notation "[[[ P ]]] c [[[ Q ]]]" := (Triple P c Q) (at level 90, c at next level).

Lemma Triple_skip: forall P,
      [[[ P ]]] SKIP [[[ P ]]].
Proof.
  intros P s PRE. apply safe_now. reflexivity. auto.
Qed.

Lemma Triple_assign: forall P x a,
      [[[ aupdate x a P ]]] ASSIGN x a [[[ P ]]].
Proof.
  intros P x a s PRE. apply safe_step.
- unfold terminated; congruence. 
- cbn; tauto.
- intros c' s' RED; inv RED. apply safe_now. reflexivity. exact PRE.
Qed.

Remark safe_seq:
  forall (Q R: assertion) (c': com),
  (forall s, Q s -> safe R c' s) ->
  forall c s, safe Q c s -> safe R (c ;; c') s.
Proof.
  intros Q R c2 QR. induction 1.
  - rewrite H. apply safe_step. unfold terminated; congruence. cbn; auto. 
    intros c' s' RED; inv RED. apply QR; auto.
    inv H2.
  - apply safe_step. unfold terminated; congruence. cbn; auto.
    intros c' s' RED; inv RED.
    + elim H; red; auto.
    + apply H2; auto.
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      [[[ P ]]] c1 [[[ Q ]]] -> [[[ Q ]]] c2 [[[ R ]]] ->
      [[[ P ]]] c1;;c2 [[[ R ]]].
Proof.
  intros. intros s PRE. apply safe_seq with Q; auto.
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      [[[ atrue b //\\ P ]]] c1 [[[ Q ]]] ->
      [[[ afalse b //\\ P ]]] c2 [[[ Q ]]] ->
      [[[ P ]]] IFTHENELSE b c1 c2 [[[ Q ]]].
Proof.
  intros; intros s PRE. apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED.
  destruct (beval b s') eqn:B.
- apply H; split; auto.
- apply H0; split; auto.
Qed.

Lemma Triple_while: forall P variant b c,
  (forall v,
     [[[ atrue b //\\ aequal variant v //\\ P ]]]
     c
     [[[ alessthan variant v //\\ P ]]])
  ->
     [[[ P ]]] WHILE b c [[[ afalse b //\\ P ]]].
Proof.
  intros P variant b c T.
  assert (REC: forall v s, P s -> aeval variant s = v ->
               safe (afalse b //\\ P) (WHILE b c) s ).
  { induction v using (well_founded_induction (Z.lt_wf 0)).
    intros. apply safe_step. unfold terminated; congruence. cbn; auto.
    intros c' s' RED; inv RED.
  - apply safe_now. red; auto. split; auto.
  - apply safe_seq with (alessthan variant (aeval variant s') //\\ P).
    + intros s'' [PRE1 PRE2]. red in PRE1. eapply H. eexact PRE1. exact PRE2. auto.
    + apply T. split; auto. split; auto. red. auto.
  }
  intros s PRE. apply REC with (aeval variant s); auto.
Qed.

Lemma Triple_havoc: forall x Q,
      [[[ aforall (fun n => aupdate x (CONST n) Q) ]]] HAVOC x [[[ Q ]]].
Proof.
  intros; intros s PRE. apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED. constructor. red; auto. apply PRE.
Qed.

Lemma Triple_assert: forall b P,
      [[[ atrue b //\\ P ]]] ASSERT b [[[ atrue b //\\ P ]]].
Proof.
  intros. intros s [PRE1 PRE2]. red in PRE1.
  apply safe_step. unfold terminated; congruence. cbn; congruence.
  intros c' s' RED; inv RED. apply safe_now; auto. red; auto. split; auto.
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      [[[ P ]]] c [[[ Q ]]] -> P' -->> P -> Q -->> Q' ->
      [[[ P' ]]] c [[[ Q' ]]].
Proof.
  intros.
  assert (REC: forall c s, safe Q c s -> safe Q' c s).
  { induction 1.
  - apply safe_now; auto.
  - apply safe_step; auto.
  }
  red; auto.
Qed.

Theorem HOARE_sound:
  forall P c Q, [[ P ]] c [[ Q ]] -> [[[ P ]]] c [[[ Q ]]].
Proof.
  induction 1.
- apply Triple_skip.
- apply Triple_assign.
- apply Triple_seq with Q; auto.
- apply Triple_ifthenelse; auto.
- apply Triple_while with a; auto.
- apply Triple_havoc; auto.
- apply Triple_assert; auto.
- apply Triple_consequence with P Q; auto.
Qed.

End Soundness2.

(** Soundness of weak Hoare logic, using a coinductive "safe" predicate *)

Module Soundness3.

CoInductive safe (Q: assertion): com -> store -> Prop :=
  | safe_now: forall c s,
      terminated c -> Q s ->
      safe Q c s
  | safe_step: forall c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q c' s') ->
      safe Q c s.

Lemma safe_terminated_inv: forall Q c s,
  safe Q c s -> terminated c -> Q s.
Proof.
  intros. inv H. auto. contradiction.
Qed.

Lemma safe_not_stuck: forall Q c s,
  safe Q c s -> ~terminated c -> ~(error c s).
Proof.
  intros. inv H. contradiction. auto.
Qed.

Lemma safe_step_inv: forall Q c s c' s',
  safe Q c s -> red (c, s) (c', s') -> safe Q c' s'.
Proof.
  intros. inv H. red in H1; subst c; inv H0. eauto.
Qed. 

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

Notation "{{{ P }}} c {{{ Q }}}" := (triple P c Q) (at level 90, c at next level).

Lemma triple_skip: forall P,
      {{{ P }}} SKIP {{{ P }}}.
Proof.
  intros P s PRE. apply safe_now. reflexivity. auto.
Qed.

Lemma triple_assign: forall P x a,
      {{{ aupdate x a P }}} ASSIGN x a {{{ P }}}.
Proof.
  intros P x a s PRE. apply safe_step.
- unfold terminated; congruence. 
- cbn; tauto.
- intros c' s' RED; inv RED. apply safe_now. reflexivity. exact PRE.
Qed.

Remark safe_seq:
  forall (Q R: assertion) (c': com),
  (forall s, Q s -> safe R c' s) ->
  forall c s, safe Q c s -> safe R (c ;; c') s.
Proof.
  intros Q R c2 QR. cofix CHR; destruct 1.
  - rewrite H. apply safe_step. unfold terminated; congruence. cbn; auto.
    intros c' s' RED; inversion RED; clear RED. rewrite <- H4. apply QR; auto. congruence.
    inv H2.
  - apply safe_step. unfold terminated; congruence. cbn; auto.
    intros c' s' RED; inversion RED.
    + elim H; red; auto.
    + apply CHR. apply H1; auto.
Defined.

Lemma triple_seq: forall P Q R c1 c2,
      {{{ P }}} c1 {{{ Q }}} -> {{{ Q }}} c2 {{{ R }}} ->
      {{{ P }}} c1;;c2 {{{ R }}}.
Proof.
  intros. intros s PRE. apply safe_seq with Q; auto.
Qed.

Lemma triple_while: forall P b c,
   {{{ atrue b //\\ P }}} c {{{ P  }}} ->
   {{{ P }}} WHILE b c {{{ afalse b //\\ P }}}.
Proof.
  intros P b c T.
  assert (REC: forall s, P s ->
               safe (afalse b //\\ P) (WHILE b c) s ).
  { cofix CHR; intros s Ps. apply safe_step. unfold terminated; congruence. cbn; auto.
    intros c' s' RED; inversion RED.
  - apply safe_now. red; auto. split; auto. congruence.
  - apply safe_seq with P.
    + intros s'' Ps''. apply CHR. auto.
    + apply T. split; auto. congruence.
  }
  intros s PRE. apply REC. auto.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      {{{ atrue b //\\ P }}} c1 {{{ Q }}} ->
      {{{ afalse b //\\ P }}} c2 {{{ Q }}} ->
      {{{ P }}} IFTHENELSE b c1 c2 {{{ Q }}}.
Proof.
  intros; intros s PRE. apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED.
  destruct (beval b s') eqn:B.
- apply H; split; auto.
- apply H0; split; auto.
Qed.

Lemma triple_havoc: forall x Q,
      {{{ aforall (fun n => aupdate x (CONST n) Q) }}} HAVOC x {{{ Q }}}.
Proof.
  intros; intros s PRE. apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED. constructor. red; auto. apply PRE.
Qed.

Lemma triple_assert: forall b P,
      {{{ atrue b //\\ P }}} ASSERT b {{{ atrue b //\\ P }}}.
Proof.
  intros. intros s [PRE1 PRE2]. red in PRE1.
  apply safe_step. unfold terminated; congruence. cbn; congruence.
  intros c' s' RED; inv RED. apply safe_now; auto. red; auto. split; auto.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      {{{ P }}} c {{{ Q }}} -> P' -->> P -> Q -->> Q' ->
      {{{ P' }}} c {{{ Q' }}}.
Proof.
  intros.
  assert (REC: forall c s, safe Q c s -> safe Q' c s).
  { cofix CH. destruct 1.
  - apply safe_now; auto.
  - apply safe_step; auto.
  }
  red; auto.
Qed.

Theorem Hoare_sound:
  forall P c Q, {{ P }} c {{ Q }} -> {{{ P }}} c {{{ Q }}}.
Proof.
  induction 1.
- apply triple_skip.
- apply triple_assign.
- apply triple_seq with Q; auto.
- apply triple_ifthenelse; auto.
- apply triple_while; auto.
- apply triple_havoc; auto.
- apply triple_assert; auto.
- apply triple_consequence with P Q; auto.
Qed.

End Soundness3.

(** Soundness of weak Hoare logic, using a step-indexed "safe" predicate *)

Module Soundness4.

Inductive safe (Q: assertion): nat -> com -> store -> Prop :=
  | safe_zero: forall c s,
      safe Q O c s
  | safe_now: forall n c s,
      terminated c -> Q s ->
      safe Q (S n) c s
  | safe_step: forall n c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q n c' s') ->
      safe Q (S n) c s.

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall n s, P s -> safe Q n c s.

Notation "{{{ P }}} c {{{ Q }}}" := (triple P c Q) (at level 90, c at next level).

(** Properties of [safe] *)

Lemma safe_mono:
  forall Q n c s, safe Q n c s -> forall n', (n' <= n)%nat -> safe Q n' c s.
Proof.
  induction 1; intros.
- replace n' with O by lia. constructor.
- destruct n'. constructor. apply safe_now; auto.
- destruct n'. constructor. apply safe_step; auto. intros. apply H2; auto. lia.
Qed.

Lemma safe_now': forall (Q: assertion) n c s,
  terminated c -> Q s -> safe Q n c s.
Proof.
  intros. destruct n. constructor. apply safe_now; auto.
Qed.

Lemma safe_terminated_inv: forall Q n c s,
  safe Q (S n) c s -> terminated c -> Q s.
Proof.
  intros. inv H. auto. contradiction.
Qed.

Lemma safe_notstuck: forall Q n c s,
  safe Q (S n) c s -> ~error c s.
Proof.
  intros. inv H.
- rewrite H1. cbn; auto.
- auto.
Qed.

Lemma safe_step_inv: forall Q n c s c' s',
  safe Q (S n) c s -> red (c, s) (c', s') -> safe Q n c' s'.
Proof.
  intros. inv H. 
- rewrite H2 in H0; inv H0.
- eauto.
Qed.

(** Deduction rules *)

Lemma triple_skip: forall P,
      {{{ P }}} SKIP {{{ P }}}.
Proof.
  intros P n s PRE. apply safe_now'. reflexivity. auto.
Qed.

Lemma triple_assign: forall P x a,
      {{{ aupdate x a P }}} ASSIGN x a {{{ P }}}.
Proof.
  intros P x a n s PRE. destruct n. constructor. apply safe_step.
- unfold terminated; congruence. 
- cbn; tauto.
- intros c' s' RED; inv RED. apply triple_skip. exact PRE.
Qed.

Remark safe_seq:
  forall (Q R: assertion) (c': com) n,
  (forall n' s, (n' < n)%nat -> Q s -> safe R n' c' s) ->
  forall c s, safe Q n c s -> safe R n (c ;; c') s.
Proof.
  intros Q R c2. induction n; intros QR c s SF.
- constructor.
- apply safe_step. unfold terminated; congruence.
  + cbn. eapply safe_notstuck; eauto.
  + intros c' s' RED. inv RED. 
    * apply QR. lia. eapply safe_terminated_inv; eauto. red; auto.
    * apply IHn. 
      intros; apply QR; auto.
      eapply safe_step_inv; eauto. 
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      {{{ P }}} c1 {{{ Q }}} -> {{{ Q }}} c2 {{{ R }}} ->
      {{{ P }}} c1;;c2 {{{ R }}}.
Proof.
  intros. intros n s PRE. apply safe_seq with Q; auto.
Qed.

Lemma triple_while: forall P b c,
   {{{ atrue b //\\ P }}} c {{{ P  }}} ->
   {{{ P }}} WHILE b c {{{ afalse b //\\ P }}}.
Proof.
  intros P b c T. red. induction n; intros s Ps. constructor.
  apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED. 
- apply triple_skip. split; auto.
- apply safe_seq with P. intros. apply safe_mono with n. apply IHn; auto. lia.
  apply T. split; auto.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      {{{ atrue b //\\ P }}} c1 {{{ Q }}} ->
      {{{ afalse b //\\ P }}} c2 {{{ Q }}} ->
      {{{ P }}} IFTHENELSE b c1 c2 {{{ Q }}}.
Proof.
  intros; intros n s PRE. destruct n. constructor.
  apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED.
  destruct (beval b s') eqn:B.
- apply H; split; auto.
- apply H0; split; auto.
Qed.

Lemma triple_havoc: forall x Q,
      {{{ aforall (fun n => aupdate x (CONST n) Q) }}} HAVOC x {{{ Q }}}.
Proof.
  intros; intros n s PRE. destruct n. constructor.
  apply safe_step. unfold terminated; congruence. cbn; auto.
  intros c' s' RED; inv RED. apply safe_now'. red; auto. apply PRE.
Qed.

Lemma triple_assert: forall b P,
      {{{ atrue b //\\ P }}} ASSERT b {{{ atrue b //\\ P }}}.
Proof.
  intros. intros n s [PRE1 PRE2]. red in PRE1.
  destruct n. constructor.
  apply safe_step. unfold terminated; congruence. cbn; congruence.
  intros c' s' RED; inv RED. apply safe_now'; auto. red; auto. split; auto.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      {{{ P }}} c {{{ Q }}} -> P' -->> P -> Q -->> Q' ->
      {{{ P' }}} c {{{ Q' }}}.
Proof.
  intros.
  assert (REC: forall n c s, safe Q n c s -> safe Q' n c s).
  { induction 1.
  - constructor.
  - apply safe_now; auto.
  - apply safe_step; auto.
  }
  red; auto.
Qed.

Theorem Hoare_sound:
  forall P c Q, {{ P }} c {{ Q }} -> {{{ P }}} c {{{ Q }}}.
Proof.
  induction 1.
- apply triple_skip.
- apply triple_assign.
- apply triple_seq with Q; auto.
- apply triple_ifthenelse; auto.
- apply triple_while; auto.
- apply triple_havoc; auto.
- apply triple_assert; auto.
- apply triple_consequence with P Q; auto.
Qed.

End Soundness4.

(** ** 2.5. Completeness *)

Module Completeness.

Import Soundness3.

(** A weakest (liberal) precondition, defined using the semantics *)

Definition sem_wp (c: com) (Q: assertion) : assertion :=
  fun s => safe Q c s.

Lemma terminated_dec: forall c, {terminated c} + {~terminated c}.
Proof.
  unfold terminated. destruct c; (left; reflexivity) || (right; discriminate).
Qed.

Lemma sem_wp_seq: forall c1 c2 Q s,
  sem_wp (c1 ;; c2) Q s -> sem_wp c1 (sem_wp c2 Q) s.
Proof.
  unfold sem_wp; cofix CH; intros c1 c2 Q s SAFE.
  destruct (terminated_dec c1).
- apply safe_now. auto.
  eapply safe_step_inv. eauto. rewrite t. constructor.
- apply safe_step. auto.
  change (~ (error (c1;;c2) s)).  eapply safe_not_stuck; eauto. unfold terminated; congruence.
  intros. apply CH. eapply safe_step_inv. eexact SAFE. constructor; auto.
Qed.

(** Show that the triple [ { sem_wp c Q } c { Q } ] is derivable using the rules
    of Hoare logic *)

Lemma Hoare_sem_wp:
  forall c Q, {{ sem_wp c Q }} c {{ Q }}.
Proof.
  induction c; intros Q.
- eapply Hoare_consequence_pre. apply Hoare_skip.
  intros s W. eapply safe_terminated_inv. eexact W. red; auto.
- eapply Hoare_consequence_pre. apply Hoare_assign.
  intros s W. 
  assert (W': safe Q SKIP (update x (aeval a s) s)).
  { eapply safe_step_inv. eexact W. apply red_assign. }
  apply safe_terminated_inv in W'. assumption. red; auto.
- apply Hoare_seq with (sem_wp c2 Q); auto.
  eapply Hoare_consequence_pre. apply IHc1.
  intros s; apply sem_wp_seq.
- apply Hoare_ifthenelse.
  + eapply Hoare_consequence_pre. apply IHc1.
    intros s [P1 P2]. replace c1 with (if beval b s then c1 else c2). 
    eapply safe_step_inv. eexact P2. constructor. rewrite P1; auto.
  + eapply Hoare_consequence_pre. apply IHc2.
    intros s [P1 P2]. replace c2 with (if beval b s then c1 else c2). 
    eapply safe_step_inv. eexact P2. constructor. rewrite P1; auto.
- eapply Hoare_consequence_post. apply Hoare_while.
  eapply Hoare_consequence_pre. apply IHc.
  + intros s [P1 P2].
    apply sem_wp_seq. eapply safe_step_inv. eexact P2. constructor. exact P1.
  + intros s [P1 P2].
    eapply safe_terminated_inv. eapply safe_step_inv. eexact P2. apply red_while_done. exact P1. red; auto.
- eapply Hoare_consequence. apply Hoare_assert.
  + intros s SAFE. 
    assert (NOTSTUCK: ~ (error (ASSERT b) s)).
    { eapply safe_not_stuck; eauto. unfold terminated; congruence. }
    assert (B: beval b s = true).
    { cbn in NOTSTUCK. destruct (beval b s); auto. }
    assert (FINAL: Q s).
    { eapply safe_terminated_inv. eapply safe_step_inv. eexact SAFE. constructor. auto. red; auto. }
    split. exact B. exact FINAL.
  + intros s; unfold aand; tauto.
- eapply Hoare_consequence_pre. apply Hoare_havoc.
  intros s W n. 
  assert (W': safe Q SKIP (update x n s)).
  { eapply safe_step_inv. eexact W. apply red_havoc. }
  apply safe_terminated_inv in W'. assumption. red; auto.
Qed.

(** Relative completeness follows *)

Theorem Hoare_complete:
  forall P c Q, {{{ P }}} c {{{ Q }}} -> {{ P }} c {{ Q }}.
Proof.
  intros. apply Hoare_consequence_pre with (sem_wp c Q). 
  apply Hoare_sem_wp.
  intros s. apply H.
Qed.

End Completeness.

(** ** 2.6. Calculating weakest preconditions and verification conditions *)

Module WP.

(** Annotated commands *)

Inductive com: Type :=
  | SKIP                                     (**r do nothing *)
  | ASSIGN (x: ident) (a: aexp)              (**r assignment: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r sequence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditional: [if b then c1 else c2] *)
  | WHILE (Inv: assertion) (b: bexp) (c1: com) (**r loop: [while b do c1 done] *)
  | ASSERT (b: bexp)                         (**r assertion (error if false) *)
  | HAVOC (x: ident).                        (**r nondeterministic assignment *)

Fixpoint erase (c: com) :=
  match c with
  | SKIP => Hoare.SKIP
  | ASSIGN x a => Hoare.ASSIGN x a
  | SEQ c1 c2 => Hoare.SEQ (erase c1) (erase c2)
  | IFTHENELSE b c1 c2 => Hoare.IFTHENELSE b (erase c1) (erase c2)
  | WHILE Inv b c => Hoare.WHILE b (erase c)
  | ASSERT b => Hoare.ASSERT b
  | HAVOC x => Hoare.HAVOC x
  end.

Fixpoint wlp (c: com) (Q: assertion) : assertion :=
  match c with
  | SKIP => Q
  | ASSIGN x a => aupdate x a Q
  | SEQ c1 c2 => wlp c1 (wlp c2 Q)
  | IFTHENELSE b c1 c2 => (atrue b //\\ wlp c1 Q) \\// (afalse b //\\ wlp c2 Q)
  | WHILE Inv b c => Inv
  | ASSERT b => atrue b //\\ Q
  | HAVOC x => aforall (fun n => aupdate x (CONST n) Q)
  end.

Fixpoint vcond (c: com) (Q: assertion) : Prop :=
  match c with
  | SKIP | ASSIGN _ _ => True
  | SEQ c1 c2 => vcond c1 (wlp c2 Q) /\ vcond c2 Q
  | IFTHENELSE b c1 c2 => vcond c1 Q /\ vcond c2 Q
  | WHILE Inv b c =>
      vcond c Inv /\
      (atrue b //\\ Inv -->> wlp c Inv) /\
      (afalse b //\\ Inv -->> Q)
  | ASSERT b => True
  | HAVOC x => True
  end.

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  vcond c Q /\ (P -->> wlp c Q).

Lemma wlp_sound: forall c Q,
  vcond c Q -> {{ wlp c Q }} erase c {{ Q }}.
Proof.
  induction c; intros Q VC; cbn.
- apply Hoare_skip.
- apply Hoare_assign.
- destruct VC as [VC1 VC2]. eapply Hoare_seq. apply IHc1; auto. apply IHc2; auto.
- destruct VC as [VC1 VC2].
  apply Hoare_ifthenelse; eapply Hoare_consequence_pre; eauto.
  + intros s. unfold aand, aor, atrue, afalse. intuition congruence.
  + intros s. unfold aand, aor, atrue, afalse. intuition congruence.
- destruct VC as (VC1 & VC2 & VC3).
  eapply Hoare_consequence_post. apply (Hoare_while Inv).
  eapply Hoare_consequence_pre. apply IHc; auto. exact VC2.
  exact VC3.
- eapply Hoare_consequence_post. apply Hoare_assert.
  intros s [P1 P2]; auto.
- apply Hoare_havoc.
Qed.

Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> {{ P }} erase c {{ Q }}.
Proof.
  intros P c Q [VC1 VC2]. eapply Hoare_consequence_pre. apply wlp_sound; auto. auto.
Qed.

End WP.

(** ** 2.7. Calculating strongest postconditions and verification conditions *)

Module SP.

Import WP.  (* for annotated  commands *)
(** Annotated commands *)

Fixpoint sp (P: assertion) (c: com) : assertion :=
  match c with
  | SKIP => P
  | ASSIGN x a => aexists (fun x0 => aexists (fun v => aequal (VAR x) v //\\ aupdate x (CONST x0) (P //\\ aequal a v)))
  | SEQ c1 c2 => sp (sp P c1) c2
  | IFTHENELSE b c1 c2 => sp (atrue b //\\ P) c1 \\// sp (afalse b //\\ P) c2
  | WHILE Inv b c => afalse b //\\ Inv
  | ASSERT b => atrue b //\\ P
  | HAVOC x => aexists (fun n => aupdate x (CONST n) P)
  end.

Fixpoint vcond (P: assertion) (c: com) : Prop :=
  match c with
  | SKIP | ASSIGN _ _ => True
  | SEQ c1 c2 => vcond P c1 /\ vcond (sp P c1) c2
  | IFTHENELSE b c1 c2 => vcond (atrue b //\\ P) c1 /\ vcond (afalse b //\\ P) c2
  | WHILE Inv b c =>
      vcond (atrue b //\\ Inv) c /\
      (P -->> Inv) /\
      (sp (atrue b //\\ Inv) c -->> Inv)
  | ASSERT b =>
      (P -->> atrue b)
  | HAVOC x => True
  end.

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  vcond P c /\ (sp P c -->> Q).

Lemma sp_sound: forall c P,
  vcond P c -> {{ P }} erase c {{ sp P c }}.
Proof.
  induction c; intros P VC; cbn.
- apply Hoare_skip.
- apply Floyd_assign.
- destruct VC as [VC1 VC2]. eapply Hoare_seq. apply IHc1; auto. apply IHc2; auto.
- destruct VC as [VC1 VC2].
  apply Hoare_ifthenelse; eapply Hoare_consequence_post; eauto.
  + intros s. unfold aand, aor, atrue, afalse; tauto.
  + intros s. unfold aand, aor, atrue, afalse; tauto.
- destruct VC as (VC1 & VC2 & VC3).
  eapply Hoare_consequence_pre. 2: eexact VC2.
  apply (Hoare_while Inv).
  eapply Hoare_consequence_post. apply IHc. eexact VC1. eexact VC3.
- red in VC. eapply Hoare_consequence_pre. apply Hoare_assert.
  intros s Ps. split; auto.
- eapply Hoare_consequence_pre. apply Hoare_havoc.
  intros s Ps n. exists (s x). cbn.
  set (s' := update x n s).
  set (s'' := update x (s x) s').
  assert (s'' = s).
  { apply functional_extensionality; intros y.
    unfold s'', s', update. destruct (string_dec x y); congruence. }
  red; cbn. fold s''. congruence.
Qed.

Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> {{ P }} erase c {{ Q }}.
Proof.
  intros P c Q [VC1 VC2]. eapply Hoare_consequence_post. apply sp_sound; auto. auto.
Qed.

End SP.




