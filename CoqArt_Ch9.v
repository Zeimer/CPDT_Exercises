Set Implicit Arguments.

Require Import List.
Import ListNotations.

Require Import JMeq.
Require Import Nat.
Require Import Omega.
Require Import Relations_3.

(* Tactics *)

Ltac gen x := generalize dependent x.

Ltac inv H := inversion H; subst.

Ltac invs := repeat
match goal with
    | H : ?f ?x1 ?x2 ?x3 = ?f ?x1' ?x2' ?x3' |- _ => inv H
    | H : ?f ?x1 ?x2 = ?f ?x1' ?x2' |- _ => inv H
    | H : ?f ?x1 = ?f ?x1' |- _ => inv H
end.

Ltac remember_vars H :=
match H with
    | ?f ?x1 => is_var x1; remember_vars f
    | ?f ?x1 =>
        let x1' := fresh "x1" in
        let H1 := fresh "H1" in remember x1 as x1' eqn: H1; remember_vars f
    | _ => idtac
end.

Ltac clean_eqs := repeat
match goal with
    | H : ?x = ?x |- _ => clear H
    | H : ?x = ?x -> _ |- _ => specialize (H eq_refl)
    | H : forall x, ?y = ?y -> ?P |- _ =>
        assert (H' := fun x => H x eq_refl); clear H; rename H' into H
end.

Ltac ind' H :=
match type of H with
    | ?T => remember_vars T; induction H; subst; try congruence;
        invs; clean_eqs; eauto
end.

Ltac term_contains t x :=
match t with
    | ?f x => idtac
    | ?f _ => term_contains f x
    | x => idtac
    | _ => fail
end.

(*Ltac term_not_contains t x :=
match t with
    | ?f x => idtac f; fail
    | ?f _ => term_not_contains f x
    | x => fail
    | _ => idtac
end.*)

Ltac gen_ind H :=
match reverse goal with
    | H : _ |- _ => fail
    | x : ?Tx |- _ =>
        match type of H with
            | ?TH => (unify TH Tx + term_contains TH x); idtac
            | _ => generalize dependent x
        end
end.

Ltac ind H := try intros until H; gen_ind H; ind' H.

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

Hint Constructors rtc Rstar.

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

Lemma wp_front :
  forall l : list par, wp l -> wp (open :: close :: l).
Proof.
  intros. change (open :: close :: l) with ([open; close] ++ l). eauto.
Qed.

Function count (acc : nat) (l : list par) : option nat :=
match l with
    | [] => Some acc
    | open :: l' => count (S acc) l'
    | close :: l' =>
        match acc with
            | 0 => None
            | S n' => count n' l'
        end
end.

Lemma count_app :
  forall (l l' : list par) (n m : nat),
    count n l = Some m -> count n (l ++ l') = count m l'.
Proof.
  intros. functional induction count n l; cbn; eauto; congruence.
Qed.

Lemma count_plus :
  forall (l : list par) (n m r : nat),
    count n l = Some r -> count (n + m) l = Some (r + m).
Proof.
  intros. functional induction count n l; cbn in *; try congruence; eauto.
Qed.

Lemma count_wp_Aux :
  forall (l : list par) (n : nat),
    count n l = Some 0 -> wp (replicate n open ++ l).
Proof.
  intros. functional induction count n l; cbn in *.
    inversion H; subst; auto.
    replace (replicate acc open ++ open :: l')
    with (open :: replicate acc open ++ l').
      apply IHo. assumption.
      rewrite app_comm_cons, replicate_rev, <- app_assoc. trivial.
    inversion H.
Abort.

Theorem count_wp :
  forall l : list par,
    count 0 l = Some 0 <-> wp l.
Proof.
  split.
    Focus 2. induction 1; cbn; auto.
      rewrite (@count_app _ _ 1 1); cbn; auto.
        apply (@count_plus _ 0 1 0). assumption.
      erewrite count_app; eauto.
    intros. remember 0 as n. functional induction count n l; cbn; auto.
      functional inversion H; subst.
Abort.

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
      rewrite <- Heql. apply wp_front. eauto.
      inversion Heql; subst.
Restart.
Admitted.

Lemma recognize_sound_aux :
  forall (n : nat) (l : list par),
    recognize n l = true -> wp (replicate n open ++ l).
Proof.
  intros n l H. functional induction recognize n l; auto; try congruence.
    replace (replicate n open ++ open :: l')
    with (open :: replicate n open ++ l').
      apply IHb. assumption.
      rewrite app_comm_cons, replicate_rev, <- app_assoc. trivial.
    cbn. apply wp_oc_new. auto.
Qed.

Theorem recognize_sound :
  forall l : list par, recognize 0 l = true -> wp l.
Proof.
  intros. change l with (replicate 0 open ++ l).
  apply recognize_sound_aux. assumption.
Qed.

(* Ex. 9.23 *)
Function parse (s : list bin) (t : bin) (l : list par) : option bin :=
match l with
    | [] =>
        match s with
            | [] => Some t
            | _ => None
        end
    | open :: l' => parse (t :: s) L l'
    | close :: l' =>
        match s with
            | t' :: s' => parse s' (N t' t) l'
            | _ => None
        end
end.

Theorem parse_complete :
  forall l : list par, wp l -> parse [] L l <> None.
Proof.
  intros. ind H; cbn. congruence.
  induction 1; cbn.
Restart.
  intros. remember [] as acc. remember L as wut.
  functional induction @parse acc wut l; subst.
    congruence.
    inv y.
    Focus 3. inv H.
Abort.

Theorem parse_invert :
  forall (l : list par) (t : bin),
    parse [] L l = Some t -> bin_to_string' t = l.
Proof.
Abort.

Theorem parse_sound :
  forall (l : list par) (t : bin), parse [] L l = Some t -> wp l.
Proof.
  intros. remember [] as acc. remember L as tr.
  gen Heqtr; gen Heqacc.
  functional induction parse acc tr l; cbn in *; intros; subst; auto.
Abort.

Section little_semantics.

Axioms Var aExp bExp : Set.

Inductive instr : Set :=
    | Skip : instr
    | Assign : Var -> aExp -> instr
    | Seq : instr -> instr -> instr
    | While : bExp -> instr -> instr.

Axiom
  (state : Set)
  (update : state -> Var -> Z -> option state)
  (evalA : state -> aExp -> option Z)
  (evalB : state -> bExp -> option bool).

Inductive exec : state -> instr -> state -> Prop :=
    | execSkip : forall s : state, exec s Skip s
    | execAssign : forall (s1 s2 : state) (v : Var) (a : aExp) (k : Z),
        evalA s1 a = Some k -> update s1 v k = Some s2 ->
        exec s1 (Assign v a) s2
    | execSeq : forall (s1 s2 s3 : state) (i1 i2 : instr),
        exec s1 i1 s2 -> exec s2 i2 s3 -> exec s1 (Seq i1 i2) s3
    | execWhileTrue : forall (s1 s2 s3 : state) (i : instr) (be : bExp),
        evalB s1 be = Some true -> exec s1 i s2 -> exec s2 (While be i) s3 ->
        exec s1 (While be i) s3
    | execWhileFalse : forall (s : state) (i : instr) (be : bExp),
        evalB s be = Some false -> exec s (While be i) s.

Hint Constructors instr exec.

(* Ex. 9.25 *)
Theorem HoareWhileRule :
  forall (P : state -> Prop) (b : bExp) (i : instr) (s s' : state),
    (forall s1 s2 : state, P s1 -> evalB s1 b = Some true ->
      exec s1 i s2 -> P s2) -> P s -> exec s (While b i) s' -> P s' /\
        evalB s' b = Some false.
Proof.
  intros. remember (While b i) as w.
  induction H1; intros; inversion Heqw; subst; eauto.
Restart.
  intros. ind H1.
Qed.

(* Ex. 9.26 *)
Theorem ex9_26 :
  forall (s : state) (be : bExp),
    evalB s be = Some true ->
      ~ exists s' : state, exec s (While be Skip) s'.
Proof.
  intros. destruct 1 as [s' Hs']. remember (While be Skip) as w.
  gen be. induction Hs'; inversion 2; subst.
    inversion Hs'1; subst. eauto.
    rewrite H in H0. congruence.
Restart.
  intros s be H [s' Hs']. ind Hs'. inv Hs'1. auto.
Qed.

Theorem ex9_26' :
  forall (s s' : state) (b : bExp),
    exec s (While b Skip) s' -> evalB s b = Some true -> False.
Proof.
  intros. ind H. inv H2. eauto.
Qed.

Theorem HoareSeq :
  forall (P : state -> Prop) (s1 s2 s3 : state) (i12 i23 : instr),
    (forall s s' : state, P s -> exec s i12 s' -> P s') ->
    (forall s s' : state, P s -> exec s i23 s' -> P s') ->
      P s1 -> exec s1 (Seq i12 i23) s3 -> P s3.
Proof.
  intros. ind H2.
Qed.

(* Ex. 9.28 *)
Goal ~ sorted le [1; 3; 2].
Proof.
  inversion 1; subst. inversion H4; subst. omega.
Qed.

(* Ex. 9.29 *)
Fixpoint nat_ind_3
  (P : nat -> Prop) (H0 : P 0) (H1 : P 1) (H2 : P 2)
  (H3 : forall n : nat, P n -> P (3 + n)) (n : nat) : P n.
Proof.
  destruct n as [| [| [| n']]]; auto.
  apply H3. apply nat_ind_3; auto.
Qed.

Theorem ex9_29 :
  forall n : nat, exists a b : nat, 8 + n = 3 * a + 5 * b.
Proof.
  induction n using nat_ind_3.
    exists 1, 1; trivial.
    exists 3, 0; trivial.
    exists 0, 2; trivial.
    destruct IHn as [a [b IH]]. exists (S a), b. omega.
Qed.

Theorem ex9_29_v2 :
  forall n : nat, 8 <= n -> exists a b : nat,
    n = 3 * a + 5 * b.
Proof.
  induction n using lt_wf_ind; intros.
  assert (n = 8 \/ n = 9 \/ n = 10 \/ 11 <= n). omega.
  destruct H1 as [H1 | [H1 | [H1 | H1]]].
    exists 1, 1; trivial.
    exists 3, 0; trivial.
    exists 0, 2; trivial.
    destruct (H (n - 3)) as [a [b IH]]; try omega. exists (S a), b. omega.
Qed.

Theorem ex9_29_v3 :
  forall n : nat, exists a b : nat, 8 + n = 3 * a + 5 * b.
Proof.
  induction n using lt_wf_ind; intros.
  destruct n as [| [| [| n']]].
    exists 1, 1; trivial.
    exists 3, 0; trivial.
    exists 0, 2; trivial.
    destruct (H n') as [a [b IH]]; try omega. exists (S a), b. omega.
Qed.