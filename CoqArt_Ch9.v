Set Implicit Arguments.

Require Import List.
Import ListNotations.

(* Ex. 9.1 *)
Inductive last {A : Type} (x : A) : list A -> Prop :=
    | last_singl : last x [x]
    | last_cons : forall (h : A) (t : list A),
        last x t -> last x (h :: t).

Hint Constructors last.

Function last_fun {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | [x] => Some x
    | h :: t => last_fun t
end.

Theorem last_spec :
  forall (A : Type) (x : A) (l : list A),
    last x l <-> last_fun l = Some x.
Proof.
  split.
    induction 1; cbn; trivial. destruct t; auto. inversion IHlast.
    functional induction @last_fun A l; inversion 1; auto.
Qed.

(** La comparaison de la difficulté: ils sont également difficiles
    á programmer. [last] a juste deux constructeurs, pendant que
    [last_fun] a trois cas de match, mais gráce á [functional
    induction] la preuve est facile en tous les deux directions. *)


(* Ex. 9.2 *)
Inductive palindrome {A : Type} : list A -> Prop :=
    | palindrome_nil : palindrome []
    | palindrome_singl : forall x : A, palindrome [x]
    | palindrome_cons_app : forall (x : A) (l : list A),
        palindrome l -> palindrome (x :: l ++ [x]).

(* Ex. 9.3 *)
Inductive rtc {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | rtc_step : forall x y : A, R x y -> rtc R x y
    | rtc_refl : forall x : A, rtc R x x
    | rtc_trans : forall x y z : A, rtc R x y -> rtc R y z -> rtc R x z.

Hint Constructors rtc.

Require Import Relations_3.

Hint Constructors Rstar.

Lemma Rstar_trans :
  forall (A : Type) (R : A -> A -> Prop), Transitive A (Rstar A R).
Proof.
  red. induction 1; eauto.
Qed.

Theorem rtc_Rstar :
  forall (A : Type) (R : A -> A -> Prop),
    forall x y : A, rtc R x y <-> Rstar A R x y.
Proof.
  split; induction 1; eauto. eapply Rstar_trans; eauto.
Qed.

(* Ex. 9.4 *)
Inductive swap {A : Type} : list A -> list A -> Prop :=
    | c_swap : forall (x y : A) (l l' : list A),
        swap (l ++ x :: y :: l') (l ++ y :: x :: l').

Hint Constructors swap.

Definition perm {A : Type} (l l' : list A) : Prop := rtc swap l l'.

Theorem Equivalence_perm :
  forall A : Type, Equivalence (list A) perm.
Proof.
  split; do 2 red; eauto. unfold perm.
  induction 1; eauto. inversion H. eauto.
Qed.

(* Ex. 9.5 *)
Inductive par : Set := open | close.

Inductive wp : list par -> Prop :=
    | wp_nil : wp []
    | wp_par : forall l : list par, wp l -> wp (open :: l ++ [close])
    | wp_app : forall l l' : list par, wp l -> wp l' -> wp (l ++ l').

Hint Constructors wp.

Theorem wp_oc : wp [open; close].
Proof.
  change [open; close] with (open :: [] ++ [close]). eauto.
Qed.

Hint Resolve wp_oc.

Theorem wp_o_head_c :
  forall l1 l2 : list par,
    wp l1 -> wp l2 -> wp (open :: l1 ++ close :: l2).
Proof.
  intros.
  replace (open :: l1 ++ close :: l2) with ((open :: l1 ++ [close]) ++ l2).
    eauto.
    cbn. rewrite <- app_assoc. trivial.
Qed.

Theorem wp_o_tail_c :
  forall l1 l2 : list par, wp l1 -> wp l2 ->
    wp (l1 ++ open :: l2 ++ [close]).
Proof. eauto. Qed.

(* Ex. 9.6 *)
Inductive bin : Set :=
    | L : bin
    | N : bin -> bin -> bin.

Function bin_to_string (t : bin) : list par :=
match t with
    | L => []
    | N l r => open :: (bin_to_string l ++ close :: bin_to_string r)
end.

Hint Resolve wp_o_head_c wp_o_tail_c.

Theorem bin_to_string_wp :
  forall t : bin, wp (bin_to_string t).
Proof.
  intro. functional induction bin_to_string t; eauto.
Qed.

(* Ex. 9.7 *)
Function bin_to_string' (t : bin) : list par :=
match t with
    | L => []
    | N l r => bin_to_string' l ++ (open :: bin_to_string' r ++ [close])
end.


Theorem bin_to_string'_wp :
  forall t : bin, wp (bin_to_string' t).
Proof.
  intro. functional induction bin_to_string' t; eauto.
Qed.

(* Ex. 9.8 *)
Require Import JMeq.
Require Import Nat.

Functional Scheme add_ind := Induction for add Sort Prop.

Theorem plus_assoc_JMeq :
  forall x y z : nat, JMeq (x + (y + z)) ((x + y) + z).
Proof.
  intros. remember (y + z) as n.
  functional induction plus x n; cbn; try rewrite IHn0; trivial.
Qed.

(** Ex. 9.9 *)
Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

Hint Constructors even.

Require Import Omega.

Theorem even_double :
  forall n : nat, even n -> exists m : nat, n = 2 * m.
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHeven as [m Hm]. exists (S m). omega.
Qed.

Theorem double_even :
  forall n : nat, even (2 * n).
Proof.
  induction n as [| n']; cbn; auto.
  replace (even _) with (even (S (S (2 * n')))).
    auto.
    f_equal. omega.
Qed.

Theorem even_square_even :
  forall n : nat, even n -> even (n * n).
Proof.
  intros. destruct (even_double H). subst.
  rewrite <- !mult_assoc. apply double_even.
Restart.
  induction 1; cbn; auto.
  constructor. rewrite plus_comm. cbn.
  constructor. rewrite mult_comm.
Abort.

(* Ex. 9.11 *)
Theorem lt_le :
  forall n p : nat, n < p -> n <= p.
Proof.
  intros. unfold lt in H. apply le_ind with (S n); auto.
Qed.

(* Ex. 9.12 *)
Definition my_le (n p : nat) :=
  forall P : nat -> Prop, P n -> (forall q : nat, P q -> P (S q)) -> P p.

Theorem le_my_le :
  forall n p : nat, n <= p -> my_le n p.
Proof.
  unfold my_le. induction 1; intros; firstorder.
Qed.

(** Ex. 9.13 *)
Theorem le_trans :
  forall a b c : nat, a <= b -> b <= c -> a <= c.
Proof.
  intros a b c H. generalize dependent c. induction 1; auto.
Qed.

Theorem my_le_trans :
  forall a b c : nat, my_le a b -> my_le b c -> my_le a c.
Proof.
  firstorder.
Restart.
  unfold my_le. intros. apply H0.
    apply H; auto.
    auto.
Qed.

(* Ex. 9.14 *)
Inductive le_diff (n m : nat) : Prop :=
  le_d : forall x : nat, x + n = m -> le_diff n m.

Hint Constructors le_diff.

Theorem le_diff_le :
  forall n m : nat, n <= m <-> le_diff n m.
Proof.
  split.
    induction 1.
      apply le_d with 0. trivial.
      destruct IHle as [x Hx]. apply le_d with (S x). omega.
    destruct 1. subst. omega.
Qed.

(* Ex. 9.15 *)
Inductive le' : nat -> nat -> Prop :=
    | le'_0 : forall n : nat, le' 0 n
    | le'_SS : forall n m : nat, le' n m -> le' (S n) (S m).

Hint Constructors le'.

Lemma le'_refl :
  forall n : nat, le' n n.
Proof.
  induction n as [| n']; auto.
Qed.

Lemma le'_S :
  forall n m : nat, le' n m -> le' n (S m).
Proof.
  induction 1; auto.
Qed.

Theorem le_le' :
  forall n m : nat, n <= m <-> le' n m.
Proof.
  split.
    induction 1.
      apply le'_refl.
      apply le'_S. assumption.
    induction 1; omega.
Qed.

(* Ex. 9.16 *)
Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | sorted_nil : sorted R []
    | sorted_singl : forall x : A, sorted R [x]
    | sorted_cons : forall (x y : A) (l : list A),
        R x y -> sorted R (y :: l) -> sorted R (x :: y :: l).

Hint Constructors sorted.

Definition sorted' (A : Type) (R : A -> A -> Prop) (l : list A) : Prop :=
  forall (l1 l2 : list A) (n1 n2 : A),
    l = l1 ++ n1 :: n2 :: l2 -> R n1 n2.

Theorem sorted_sorted' :
  forall (A : Type) (R : A -> A -> Prop) (l : list A),
    sorted R l <-> sorted' R l.
Proof.
  unfold sorted'. split.
    Focus 2. destruct l as [| h t]; auto. generalize dependent h.
      induction t as [| h' t']; intros; auto. constructor.
        apply (H [] t' h h'). trivial.
        apply IHt'. intros. apply (H (h :: l1) l2 n1 n2). rewrite H0. auto.
    induction 1; intros.
      destruct l1; inversion H.
      destruct l1 as [| h [| h' t]]; inversion H.
      destruct l1; inversion H1; subst; eauto.
Qed.

(* Ex. 9.17 *)
(* TODO *)

(* Ex. 9.18 *)
Section weird_induc_proof.

Variable P : nat -> Prop.
Variable f : nat -> nat.

Hypothesis f_strict_mono :
  forall n m : nat, lt n m -> lt (f n) (f m).

Hypothesis f_0 : lt 0 (f 0).

Hypothesis P0 : P 0.
Hypothesis P_Sn_n : forall n : nat, P (S n) -> P n.
Hypothesis f_P : forall n : nat, P n -> P (f n).

Lemma f_expanding :
  forall n : nat, n < f n.
Proof.
  induction n as [| n'].
    apply f_0.
    assert (f n' < f (S n')).
      apply f_strict_mono. omega.
      omega.
Qed.

Lemma P_decrease :
  forall n m : nat, n < m -> P m -> P n.
Proof.
  induction 1; intro.
    apply P_Sn_n. assumption.
    apply IHle. apply P_Sn_n. assumption.
Qed.

Theorem weird_induc : forall n : nat, P n.
Proof.
  induction n as [| n'].
    apply P0.
    destruct (Nat.eq_dec (S n') (f n')).
      rewrite e. apply f_P. assumption.
      assert (S n' < f n').
        pose (f_expanding n'). omega.
        cut (P (f n')).
          intro. apply P_decrease with (f n'); assumption.
          apply f_P. assumption.
Qed.

End weird_induc_proof.

(* Ex. 9.19 *)
Inductive wp' : list par -> Prop :=
    | wp'_nil : wp' []
    | wp'_cons : forall l1 l2 : list par,
        wp' l1 -> wp' l2 -> wp' (open :: l1 ++ close :: l2).

Hint Constructors wp'.

Lemma wp'_app :
  forall l l' : list par, wp' l -> wp' l' -> wp' (l ++ l').
Proof.
  induction 1; intros; cbn; auto.
  rewrite <- app_assoc. rewrite <- app_comm_cons. eauto.
Qed.

Hint Resolve wp'_app.

Theorem wp_wp' :
  forall l : list par, wp l <-> wp' l.
Proof.
  split; induction 1; eauto.
Qed.

(* Ex. 9.20 *)
Inductive wp'' : list par -> Prop :=
    | wp''_nil : wp'' []
    | wp''_cons : forall l1 l2 : list par,
        wp'' l1 -> wp'' l2 -> wp'' (l1 ++ open :: l2 ++ [close]).

Hint Constructors wp''.

Lemma wp''_app :
  forall l l' : list par, wp'' l -> wp'' l' -> wp'' (l ++ l').
Proof.
  intros l l' Hl H'. generalize dependent l.
  induction H'; intros.
    rewrite app_nil_r. assumption.
    rewrite app_comm_cons. rewrite app_assoc. apply wp''_cons; eauto.
Qed.

Hint Resolve wp''_app.

Theorem wp_wp'' :
  forall l : list par, wp l <-> wp'' l.
Proof.
  split; induction 1; eauto.
    change (open :: l ++ [close]) with ([] ++ open :: l ++ [close]). auto.
Qed.

(* Ex. 9.21 *)
Function recognize (n : nat) (l : list par) : bool :=
match l, n with
    | [], 0 => true
    | [], _ => false
    | open :: l', _ => recognize (S n) l'
    | close :: _, 0 => false
    | close :: l', (S n') => recognize n' l'
end.

Lemma recognize_complete_aux :
  forall l : list par, wp l ->
    forall (n : nat) (l' : list par),
      recognize n (l ++ l') = recognize n l'.
Proof.
  induction 1; intros; cbn; auto; rewrite <- app_assoc.
    rewrite IHwp. cbn. trivial.
    rewrite IHwp1, IHwp2. trivial.
Qed.

Theorem recognize_complete :
  forall l : list par, wp l -> recognize 0 l = true.
Proof.
  intros. rewrite <- (app_nil_r l). rewrite recognize_complete_aux; auto.
Qed.

(* Ex. 9.22 *)
Function replicate {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: replicate n' x
end.

Lemma replicate_rev :
  forall (A : Type) (n : nat) (x : A),
    x :: replicate n x = replicate n x ++ [x].
Proof.
  intros. functional induction @replicate A n x.
    trivial.
    cbn. rewrite IHl. trivial.
Qed.

Lemma wp_oc_new :
  forall l1 l2 : list par,
    wp (l1 ++ l2) -> wp (open :: l1 ++ close :: l2).
Proof.
  intros. remember (l1 ++ l2) as l.
  generalize dependent l2. generalize dependent l1.
  induction H; intros; subst.
    assert (l1 = [] /\ l2 = []).
      apply app_eq_nil. auto.
      destruct H. subst. auto.
    destruct l1 as [| [] t]; cbn in *.
Restart.
  
Admitted.

Function recognize' (n : nat) (l : list par) : bool :=
match n, l with
    | 0, [] => true
    | _, [] => false
    | _, open :: l' => recognize (S n) l'
    | 0, close :: _ => false
    | S n', close :: l' => recognize n' l'
end.

Lemma recognize_sound_aux :
  forall (n : nat) (l : list par),
    recognize n l = true -> wp (replicate n open ++ l).
Proof.
  intros n l H. functional induction recognize n l; auto; try congruence.
    replace (replicate n open ++ open :: l')
    with (open :: replicate n open ++ l').
      apply IHb. assumption.
      rewrite app_comm_cons, replicate_rev, <- app_assoc. trivial. Search wp.
    cbn. apply wp_oc_new. auto.
Restart.
  intros n l. generalize dependent n.
  induction l as [| h t]; cbn.
    destruct n as [| n']; cbn; inversion 1; auto.
    destruct n as [| n'], h; cbn.
      apply IHt.
      inversion 1.
      intros. replace (open :: replicate n' open ++ open :: t)
        with (open :: (replicate n' open ++ [open]) ++ t).
        rewrite <- replicate_rev. cbn. specialize (IHt _ H). apply IHt.
        f_equal. rewrite <- app_assoc. cbn. trivial.
        intros.
Restart.
  induction n as [| n'].
    destruct l; cbn; inversion 1; auto. destruct p.
Abort.

Lemma recognize'_sound_aux :
  forall (n : nat) (l : list par),
    recognize' n l = true -> wp (replicate n open ++ l).
Proof.
  induction n as [| n'].
    induction l as [| [] t]; cbn; auto.
      destruct t.
Restart.
  intros. functional induction recognize' n l; cbn; auto. Print wp.
    rewrite app_nil_r. destruct n; inversion y; congruence.
    destruct l'; inversion H. destruct p. inversion H1.
Abort.

Theorem recognize_sound :
  forall l : list par, recognize 0 l = true -> wp l.
Proof.
  intros. remember 0 as n. generalize dependent Heqn.
  functional induction recognize n l; intros; subst; auto.
    remember 1 as m. functional induction recognize m l'; subst;
    try congruence; try omega.
Restart.
  induction l as [| h t]; cbn; intros; auto.
  destruct h.
    destruct t; cbn in *.
      inversion H.
      destruct p.

Abort.

