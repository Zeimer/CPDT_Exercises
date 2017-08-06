From mathcomp Require Import ssreflect.

(* Ex. 1 *)
Inductive truth : Type :=
    | No : truth
    | Maybe : truth
    | Yes : truth.

Definition not (t : truth) : truth :=
match t with
    | No => Yes
    | Maybe => Maybe
    | Yes => No
end.

Definition and (t1 t2 : truth) : truth :=
match t1, t2 with
    | Yes, _ => t2
    | No, _ => No
    | _, Yes => t1
    | _, No => No
    | _, _ => Maybe
end.

Definition or (t1 t2 : truth) : truth :=
match t1, t2 with
    | Yes, _ => Yes
    | No, _ => t2
    | _, Yes => Yes
    | _, No => t1
    | _, _ => Maybe
end.

Ltac solve_truth := intros; repeat
match goal with
    | t : truth |- _ => destruct t
end; cbn in *; auto.

Theorem and_comm :
  forall t1 t2 : truth, and t1 t2 = and t2 t1.
Proof.
  solve_truth.
Qed.

Theorem or_comm :
  forall t1 t2 : truth, or t1 t2 = or t2 t1.
Proof.
  solve_truth.
Qed.

Theorem and_or_distr :
  forall a b c : truth, and a (or b c) = or (and a b) (and a c).
Proof.
  solve_truth.
Qed.

Theorem or_and_distr :
  forall a b c : truth, or a (and b c) = and (or a b) (or a c).
Proof.
  solve_truth.
Qed.

Theorem not_and :
  forall t1 t2 : truth, not (and t1 t2) = or (not t1) (not t2).
Proof.
  solve_truth.
Qed.

Theorem not_or :
  forall t1 t2 : truth, not (or t1 t2) = and (not t1) (not t2).
Proof.
  solve_truth.
Qed.

(* Ex. 2 *)
Require Import List.
Import ListNotations.

Inductive slist (A : Type) : Type :=
    | snil : slist A
    | ssingl : A -> slist A
    | sapp : slist A -> slist A -> slist A.

Arguments snil [A].
Arguments ssingl [A] _.
Arguments sapp [A] _ _.

Fixpoint flatten {A : Type} (l : slist A) : list A :=
match l with
    | snil => []
    | ssingl x => [x]
    | sapp l1 l2 => flatten l1 ++ flatten l2
end.

Theorem flatten_sapp_distr :
  forall (A : Type) (l1 l2 : slist A),
    flatten (sapp l1 l2) = flatten l1 ++ flatten l2.
Proof.
  by [].
Qed.

(* Ex. 3 *)

Inductive binop : Set := Plus | Times.

Definition var : Set := nat.

Inductive exp : Set :=
    | Const : nat -> exp
    | Binop : binop -> exp -> exp -> exp
    | Var : var -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
match b with
    | Plus => plus
    | Times => mult
end.

Fixpoint expDenote (ctx : var -> nat) (e : exp) : nat :=
match e with
    | Const n => n
    | Binop b e1 e2 => binopDenote b (expDenote ctx e1) (expDenote ctx e2)
    | Var v => ctx v
end.

Fixpoint cfold (e : exp) : exp :=
match e with
    | Const n => Const n
    | Binop b e1 e2 =>
        match cfold e1, cfold e2 with
            | Const n, Const m => Const (binopDenote b n m)
            | e1', e2' => Binop b e1' e2'
        end
    | Var v => Var v
end.

Theorem cfold_correct :
  forall (ctx : var -> nat) (e : exp),
    expDenote ctx (cfold e) = expDenote ctx e.
Proof.
  intros.
  elim: e ctx => [n | b e1 IHe1 e2 IHe2 | v] ctx //=.
    case: (cfold e1) IHe1 IHe2.
Restart.
  induction e; cbn; try destruct (cfold e1), (cfold e2); cbn; auto.
Qed.

Inductive instr : Set :=
    | iConst : nat -> instr
    | iBinop : binop -> instr.

Definition prog : Type := list instr.
Definition stack : Type := list nat.

Definition instrDenote (i : instr) (s : stack) : option stack :=
match i with
    | iConst n => Some (n :: s)
    | iBinop b => match s with
        | x :: y :: s' => Some (binopDenote b x y :: s')
        | _ => None
    end
end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
match p with
    | [] => Some s
    | i :: p' => match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
    end
end.

Fixpoint compile (ctx : var -> nat) (e : exp) : prog :=
match e with
    | Const n => [iConst n]
    | Binop b e1 e2 => compile ctx e2 ++ compile ctx e1 ++ [iBinop b]
    | Var v => [iConst (ctx v)]
end.

Lemma compile_correct' :
  forall (e : exp) (ctx : var -> nat) (p : prog) (s : stack),
    progDenote (compile ctx e ++ p) s = progDenote p (expDenote ctx e :: s).
Proof.
  induction e; cbn; intros; trivial.
    by rewrite -!app_assoc IHe2 IHe1.
Qed.

Theorem compile_correct :
  forall (e : exp) (ctx : var -> nat),
    progDenote (compile ctx e) [] = Some [expDenote ctx e].
Proof.
  destruct e; cbn; intros; trivial.
    by rewrite !compile_correct'.
Qed.

(* Ex. 4 *)
Require Import Arith.

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
    | TPlus : tbinop Nat Nat Nat
    | TTimes : tbinop Nat Nat Nat
    | TEq : forall t : type, tbinop t t Bool
    | TLt : tbinop Nat Nat Bool.

Inductive nat_exp : Set :=
    | TNConst : nat -> nat_exp
    | TNBinop : tbinop Nat Nat Nat -> nat_exp -> nat_exp -> nat_exp
    | TNVar : var -> nat_exp
    | TNIf : bool_exp -> nat_exp -> nat_exp -> nat_exp

with bool_exp : Set :=
    | TBConst : bool -> bool_exp
    | TBBinop : tbinop Nat Nat Bool -> nat_exp -> nat_exp -> bool_exp.

Definition typeDenote (t : type) : Set :=
match t with
    | Nat => nat
    | Bool => bool
end.

Definition tbinopDenote {t1 t2 t3 : type} (b : tbinop t1 t2 t3)
    : typeDenote t1 -> typeDenote t2 -> typeDenote t3 :=
match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => Bool.eqb
    | TLt => leb
end.

Function nat_exp_denote (ctx : var -> nat) (e : nat_exp) : typeDenote Nat :=
match e with
    | TNConst n => n
    | TNBinop op e1 e2 =>
        (tbinopDenote op) (nat_exp_denote ctx e1) (nat_exp_denote ctx e2)
    | TNVar v => ctx v
    | TNIf b e1 e2 =>
        if bool_exp_denote ctx b
        then nat_exp_denote ctx e1
        else nat_exp_denote ctx e2
end
with bool_exp_denote (ctx : var -> nat) (b : bool_exp) : typeDenote Bool :=
match b with
    | TBConst true => true
    | TBConst false => false
    | TBBinop op e1 e2 =>
        (tbinopDenote op) (nat_exp_denote ctx e1) (nat_exp_denote ctx e2)
end.

Function nat_cfold (ctx : var -> nat) (e : nat_exp) : nat_exp :=
match e with
    | TNConst n => TNConst n
    | TNBinop op e1 e2 =>
        match nat_cfold ctx e1, nat_cfold ctx e2 with
            | TNConst n, TNConst m => TNConst (tbinopDenote op n m)
            | e1', e2' => TNBinop op e1' e2'
        end
    | TNVar v => TNVar v
    | TNIf b e1 e2 =>
        match bool_cfold ctx b with
            | TBConst true => nat_cfold ctx e1
            | TBConst false => nat_cfold ctx e2
            | b' => TNIf b' (nat_cfold ctx e1) (nat_cfold ctx e2)
        end
end
with bool_cfold (ctx : var -> nat) (b : bool_exp) : bool_exp :=
match b with
    | TBConst b' => TBConst b'
    | TBBinop op e1 e2 =>
        match nat_cfold ctx e1, nat_cfold ctx e2 with
            | TNConst n, TNConst m => TBConst (tbinopDenote op n m)
            | e1', e2' => TBBinop op e1' e2'
        end
end.

Scheme Nat_Bool_mut_ind := Induction for nat_exp Sort Prop
with Bool_Nat_mut_ind := Induction for bool_exp Sort Prop.

Ltac des :=
match goal with
    | |- context [match ?f ?x ?y with _ => _ end] => destruct (f x y)
    | |- context [if ?f ?x ?y then _ else _] => destruct (f x y)
end.

Theorem nat_cfold_correct :
  forall (ctx : var -> nat) (e : nat_exp),
    nat_exp_denote ctx (nat_cfold ctx e) = nat_exp_denote ctx e.
Proof.
  intro.
  induction e using Nat_Bool_mut_ind with
    (P0 := fun b =>
      bool_exp_denote ctx (bool_cfold ctx b) = bool_exp_denote ctx b);
  try (cbn; auto; fail).
    cbn. destruct (nat_cfold ctx e1), (nat_cfold ctx e2); cbn in *; auto.
      rewrite nat_cfold_equation. destruct (bool_cfold ctx b).
        destruct b0. rewrite !nat_exp_denote_equation.
      
      rewrite -IHe1. destruct (bool_cfold ctx b).
      destruct b0.
        rewrite nat_exp_denote_equation.
    cbn. induction b.
      destruct b; auto.
      repeat des; auto.
    Focus 2. cbn.
Restart.
  intros. functional induction nat_cfold ctx e; try (cbn; auto; fail).
    cbn. rewrite e3 in IHn. rewrite e4 in IHn0. cbn in *. auto.
    rewrite nat_exp_denote_equation. destruct (nat_cfold ctx e1).
      rewrite nat_exp_denote_equation. Focus 3.
    destruct b.
      destruct b; cbn in *; congruence.
      des. auto. destruct t. cbn in e3. auto.
    des; auto.
    Focus 3. destruct (bool_cfold ctx b). destruct b0; inversion y.
    Focus 2. des; auto.
    
Prove that constant-folding a natural number expression preserves its
meaning.

Eval simpl in texpDenote (TNConst 42).
Eval simpl in texpDenote (TBConst true).

(** *** 2.2.2 Target Language *)

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
    | TiNConst : forall (ts : tstack), nat -> tinstr ts (Nat :: ts)
    | TiBConst : forall (ts : tstack), bool -> tinstr ts (Bool :: ts)
    | TiBinop : forall (t1 t2 t3 : type) (ts : tstack),
        tbinop t1 t2 t3 -> tinstr (t1 :: t2 :: ts) (t3 :: ts).

Inductive tprog : tstack -> tstack -> Set :=
    | TNil : forall ts : tstack, tprog ts ts
    | TCons : forall (ts1 ts2 ts3 : tstack),
        tinstr ts1 ts2 -> tprog ts2 ts3 -> tprog ts1 ts3.

Arguments TCons [ts1 ts2 ts3] _ _.

Fixpoint vstack (ts : tstack) : Set :=
match ts with
    | [] => unit
    | h :: t => typeDenote h * vstack t
end%type.

Definition tinstrDenote {ts ts' : tstack} (i : tinstr ts ts')
    : vstack ts -> vstack ts' :=
match i with
    | TiNConst _ n => fun vs => (n, vs)
    | TiBConst _ b => fun vs => (b, vs)
    | TiBinop t1 t2 _ _ op => fun vs =>
        let '(x1, (x2, rest)) := vs in (tbinopDenote op x1 x2, rest)
end.

Fixpoint tprogDenote {ts ts' : tstack} (p : tprog ts ts')
    : vstack ts -> vstack ts' :=
match p with
    | TNil _ => fun vs => vs
    | TCons _ _ _ i p' => fun vs => tprogDenote p' (tinstrDenote i vs)
end.

(** *** 2.2.3 Translation *)

Fixpoint tconcat {ts1 ts2 ts3 : tstack} (p : tprog ts1 ts2)
    : tprog ts2 ts3 -> tprog ts1 ts3 :=
match p with
    | TNil _ => fun p'' => p''
    | TCons _ _ _ i p' => fun p'' => TCons i (tconcat p' p'')
end.

Fixpoint tcompile {t : type} (e : texp t) (ts : tstack)
    : tprog ts (t :: ts) :=
match e with
    | TNConst n => TCons (TiNConst ts n) (TNil _)
    | TBConst b => TCons (TiBConst ts b) (TNil _)
    | TBinop _ _ _ op e1 e2 =>
        tconcat (tcompile e2 _)
            (tconcat (tcompile e1 _) (TCons (TiBinop _ op) (TNil _)))
end.

Print tcompile.

Eval simpl in tprogDenote (tcompile (TNConst 42) []) tt.
Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 42)
    (TNConst 42)) (TNConst 42)) []) tt.

(** *** 2.2.4 Translation Correctness *)

Theorem tconcat_assoc :
  forall (ts1 ts2 ts3 ts4 : tstack)
  (p1 : tprog ts1 ts2) (p2 : tprog ts2 ts3) (p3 : tprog ts3 ts4),
    tconcat p1 (tconcat p2 p3) = tconcat (tconcat p1 p2) p3.
Proof.
  induction p1; simpl; intros; try rewrite IHp1; trivial.
Qed.

Theorem tcompile_correct' :
  forall (t : type) (e : texp t) (ts1 ts2 : tstack) (vs : vstack ts1)
  (p : tprog (t :: ts1) ts2),
    tprogDenote (tconcat (tcompile e ts1) p) vs =
    tprogDenote p (texpDenote e, vs).
Proof.
  induction e; simpl; intros.
    trivial.
    trivial.
    repeat rewrite <- tconcat_assoc. rewrite IHe2, IHe1.
      simpl. trivial.
Qed.

Theorem tcompile_correct : forall (t : type) (e : texp t),
    tprogDenote (tcompile e []) tt = (texpDenote e, tt).
Proof.
  destruct e; simpl; trivial.
    repeat rewrite tcompile_correct'. simpl. trivial.
Qed.

Lemma tconcat_correct :
  forall (ts1 ts2 ts3 : tstack) (p1 : tprog ts1 ts2) (p2 : tprog ts2 ts3)
  (vs : vstack ts1),
    tprogDenote (tconcat p1 p2) vs = tprogDenote p2 (tprogDenote p1 vs).
Proof.
  induction p1; simpl; intros; try rewrite IHp1; trivial.
Qed.

Hint Rewrite tconcat_correct.

Lemma tcompile_correct'' :
  forall (t : type) (e : texp t) (ts : tstack) (vs : vstack ts),
    tprogDenote (tcompile e ts) vs = (texpDenote e, vs).
Proof.
  induction e; simpl; intros; trivial.
  repeat rewrite tconcat_correct. simpl. rewrite IHe2, IHe1. trivial.
Restart.
  induction e; crush.
Qed.

Hint Rewrite tcompile_correct''.

Theorem tcompile_correct''' : forall (t : type) (e : texp t),
    tprogDenote (tcompile e []) tt = (texpDenote e, tt).
Proof. crush. Qed.