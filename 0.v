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
    match b with
      | TBConst true => nat_cfold ctx e1
      | TBConst false => nat_cfold ctx e2
      | TBBinop op e1' e2' =>
        match nat_cfold ctx e1', nat_cfold ctx e2' with
          | TNConst n, TNConst m =>
            if tbinopDenote op n m
            then nat_cfold ctx e1
            else nat_cfold ctx e2
          | e1'', e2'' => TNIf (TBBinop op e1'' e2'') e1 e2
        end
    end
end.

Theorem nat_cfold_correct :
  forall (ctx : var -> nat) (e : nat_exp),
    nat_exp_denote ctx (nat_cfold ctx e) = nat_exp_denote ctx e.
Proof.
  intros. functional induction nat_cfold ctx e; try (cbn; auto; fail).
    by rewrite 2!nat_exp_denote_equation -IHn e3 -IHn0 e4.
    rewrite IHn1 [_ ctx (TNIf _ _ _)]nat_exp_denote_equation.
      by rewrite bool_exp_denote_equation -IHn e4 -IHn0 e5 e6.
    rewrite IHn1 [_ ctx (TNIf _ _ _)]nat_exp_denote_equation.
      rewrite bool_exp_denote_equation -IHn e4 -IHn0 e5 //=.
      by case: (tbinopDenote op n m) y.
    rewrite nat_exp_denote_equation [_ ctx (TNIf _ _ _)]nat_exp_denote_equation.
      by rewrite !bool_exp_denote_equation IHn IHn0.
Qed.

(* Ex. 5 *)
Inductive nevn : Set :=
    | neZ : nevn
    | neS : nodd -> nevn

with nodd : Set :=
    | noS : nevn -> nodd.

Fixpoint wut (n : nat) : nevn + nodd :=
match n with
    | 0 => inl neZ
    | S n' =>
        match wut n' with
            | inl e => inr (noS e)
            | inr o => inl (neS o)
        end
end.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Theorem wut_pres_S :
  forall n m : nat, wut (S n) = wut (S m) -> wut n = wut m.
Proof.
  elim => [| n' IH] [| m'] //=.
    by case: (wut m').
    by case: (wut n').
    by case: (wut n'); case: (wut m'); inversion 1.
Qed.

Theorem wut_inj : injective wut.
Proof.
  red. elim => [| x' IHx] [| y'] //.
    cbn. by case: (wut y').
    cbn. by case: (wut x').
    move=> H. f_equal. by apply IHx, wut_pres_S.
Qed.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

Scheme nevn_nodd_ind := Induction for nevn Sort Prop
with nodd_nevn_ind := Induction for nodd Sort Prop.

Theorem wut_sur_nevn :
  forall e : nevn, exists n : nat, wut n = inl e
with wut_sur_nodd :
  forall o : nodd, exists n : nat, wut n = inr o.
Proof.
  case => [| o].
    by exists 0.
    destruct (wut_sur_nodd o). exists (S x). cbn. by rewrite H.
  case => [e].
    destruct (wut_sur_nevn e). exists (S x). cbn. by rewrite H.
Qed.

Theorem wut_sur : surjective wut.
Proof.
  red. case.
    apply wut_sur_nevn.
    apply wut_sur_nodd.
Qed.

Function nevn_add (n m : nevn) : nevn :=
match n, m with
    | neZ, _ => m
    | _, neZ => n
    | neS o, neS o' => neS (noS (nodd_add o o'))
end
with nodd_add (n m : nodd) : nevn :=
match n, m with
    | noS e, noS e' => neS (noS (nevn_add e e'))
end.

Theorem nevn_add_comm :
  forall n m : nevn, nevn_add n m = nevn_add m n
with nodd_add_comm :
  forall n m : nodd, nodd_add n m = nodd_add m n.
Proof.
  destruct n.
    cbn. destruct m; cbn; auto.
    destruct m.
      reflexivity.
      rewrite !nevn_add_equation. do 2 f_equal. apply nodd_add_comm.
  destruct n, m. rewrite !nodd_add_equation. do 2 f_equal. auto.
Qed.