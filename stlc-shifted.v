Require Import Strings.String.
Require Import Strings.Ascii.

Open Scope string_scope.

Require Import Bool.
Require Import Nat.

Require Import ssreflect.

(* I would like all of this crap to be isolated, done once and for all. *)
(*Module shifted_names.*)
  Require Import Omega.

  Definition Var := (string * nat)%type.
  Search "=?".

  Delimit Scope var_scope with var.
  Local Open Scope var_scope.

  Local Open Scope lazy_bool_scope.

  Fixpoint var_eqb (x1 x2 : Var) : bool :=
    match x1, x2 with
    | (s1, n1), (s2, n2) => (s1 =? s2)%string &&& (n1 =? n2)%nat
    end.

  Infix "=?" := var_eqb : var_scope.

  Create HintDb VarDB.

  Hint Resolve String.eqb_spec : VarDB.
  Hint Resolve Nat.eqb_spec : VarDB.
  Hint Resolve ReflectF : VarDB.
  Hint Resolve ReflectT : VarDB.
  Hint Extern 5 (eqb _ _ %nat) => case: Nat.eqb_spec : VarDB.

  Lemma var_eqb_spec : forall v1 v2, (reflect (v1 = v2) (v1 =? v2)).
  Proof.
    intros.
    case v1.
    case v2.
    intros.
    simpl.
    auto with VarDB.
    case: String.eqb_spec; intuition; subst; auto; try (apply ReflectF; intuition; by inversion H).
    case: Nat.eqb_spec; intuition; subst; auto; apply ReflectF; intuition; by inversion H.
  Qed.

  Hint Resolve var_eqb_spec : VarDB.

  Definition var_dec : forall v1 v2 : Var, {v1 = v2} + {v1 <> v2}.
  Proof.
    intros v1 v2.
    case: (var_eqb_spec v1 v2); auto.
  Defined.

  Ltac tvar_eqb :=
  repeat first [ congruence
               | progress subst
               | apply conj
               | match goal with
                 | [ |- context[var_eqb ?x ?y] ] => destruct (var_eqb_spec x y)
                 end
               | intro ].

  Hint Resolve var_eqb_spec.

  Lemma var_eqb_refl x : (x =? x)%var = true.
  Proof. tvar_eqb. Qed.

  Lemma var_eqb_sym x y : (x =? y)%var = (y =? x)%var.
  Proof. tvar_eqb. Qed.

  Lemma var_eqb_eq x y : (x =? y)%var = true <-> y = x.
  Proof. tvar_eqb. Qed.

  Lemma var_eqb_neq x y : (x =? y)%var = false <-> y <> x.
  Proof. tvar_eqb. Qed.

  Lemma var_eqb_compat: Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) var_eqb.
  Proof. tvar_eqb. Qed.

  (*
  (* Hm, might need a type class here. *)
  Parameter Term : Type.
  Parameter var_inj : Var -> Term.
  Parameter var_prj : Term -> Var.
  Parameter var_retraction : forall v, (var_prj (var_inj v)) = v.
  Parameter var0 : Term.

  Definition open_var (x y : Var) : Term :=
    match x, y with
     | (s, n), (s',n') =>
       (if (s =? s')%string then
          (if (n' <=? n)%nat then
             (var_inj (s , (S n)))
           else
             (var_inj y))
        else (var_inj y))
     end.

  Definition close_var (x y : Var) : Term :=
    (if (x =? y)%var then
       var0
     else
       (match x,y with
        | (s' , n'), (s, n) => (if (s =? s')%string then
                          (if (n' <? n)%nat then
                             (var_inj (s , (Nat.pred n)))
                           else
                             (var_inj y))
                        else
                          (var_inj y))
        end)).

  Lemma var_shift_right_identity (x y : Var) : (close_var x (open_var x y)) = x.
   *)

(*End shifted_names.*)

(*Import shifted_names.*)

Inductive STLCA : Type :=
| unit : STLCA
| arr (A : STLCA) (b : STLCA) : STLCA.

Inductive STLCE : Type :=
| varex (v : Var) : STLCE
| varen (n : nat) : STLCE
| lambdae (A : STLCA) (body : STLCE) : STLCE
| appe (e1 : STLCE) (e2 : STLCE) : STLCE.

Fixpoint open (x : Var) (e : STLCE) : STLCE :=
  match e with
  | varen 0 => varex x
  | varen (S n) => varen n
  | varex (s , n) => (match x with
                      | (s' , n') => (if (s =? s')%string then
                                        (if (n' <=? n) then
                                           (varex (s , (S n)))
                                         else
                                        e)
                                      else e)
                     end)
  | lambdae A body => lambdae A (open x body)
  | appe e1 e2 => (appe (open x e1) (open x e2))
  end.

Fixpoint close (x : Var) (e : STLCE) : STLCE :=
  match e with
  | varen n => varen (S n)
  | varex (s , n) => (if (var_eqb (s , n) x) then
                        varen 0
                      else
                        (match x with
                         | (s' , n') => (if (s =? s')%string then
                                           (if (n' <? n)%nat then
                                              (varex (s , (Nat.pred n)))
                                            else
                                              e)
                                         else
                                           e)
                     end))
  | lambdae A body => lambdae A (close x body)
  | appe e1 e2 => (appe (close x e1) (close x e2))
  end.

(*
Random testing stuff.
Require Import QuickChick.QuickChick.
Import QcDefaultNotation.
Open Scope qc_scope.
Import GenLow GenHigh.

Fixpoint genSTLCA (sz : nat) : G (STLCA) :=
  match sz with
  | 0 => returnGen unit
  | S x => freq [ (1, returnGen unit) ;
                  (sz, liftGen2 arr (genSTLCA x) (genSTLCA x))]
  end.

Instance show_STLCA : Show STLCA :=
  {| show :=
       let fix loop a :=
           match a with
           | unit => "unit"
           | arr A B => (loop A) ++ "->" ++ (loop B)
           end
       in loop
  |}.



Instance show_STLCE : Show STLCE :=
  {| show :=
       let fix loop a :=
           match a with
           | varex (s , n) => s
           | varen n => show n
           | lambdae A body => "λ :" ++ (show A) ++ "." ++ loop body
           | appe e1 e2 => "(" ++ loop e1 ++ " " ++ loop e2 ++ ")"
           end
       in loop
  |}.

Definition genVar : G Var :=
  liftGen2 pair (oneOf [returnGen "x" ; returnGen "y" ; returnGen "z"])
 (choose(0, 100)).

Fixpoint genSTLCE (sz : nat) : G (STLCE) :=
  match sz with
  | 0 => oneOf [ liftGen varen (choose(0, 100)) ;
                 liftGen varex genVar]
  | S x => freq [ (sz, liftGen2 lambdae (genSTLCA x)
                                (genSTLCE x)) ;
                   (sz, liftGen2 appe (genSTLCE x)
                                (genSTLCE x))]
  end.

Fixpoint stlca_eqb (A B : STLCA) : bool :=
  match (A , B) with
  | (unit , unit) => true
  | ((arr A B) , (arr A' B')) => (stlca_eqb A A') && (stlca_eqb B B')
  | _ => false
  end.

Fixpoint stlc_eqb (e1 e2 : STLCE) : bool :=
  match (e1, e2) with
  | (varen n, varen n') => (n =? n')%nat
  | (varex v , (varex v')) => (var_eqb v v')
  | ((lambdae A e) , (lambdae A' e')) => (stlca_eqb A A') && (stlc_eqb e e')
  | ((appe e1 e2) , (appe e1' e2')) => (stlc_eqb e1 e1') && (stlc_eqb e2 e2')
  | _ => false
  end.

Definition right_identityP x e := (stlc_eqb (close x (open x e)) e).
QuickChick ((forAll genVar) (fun v => (forAll (genSTLCE 5) (right_identityP v)))).

*)

Example eg1 : STLCE := open ("foo" , 0) (varen 0).
Eval compute in eg1.
Example eg2 : STLCE := open ("foo" , 0) (lambdae unit (varen 1)).
Eval compute in eg2.
Example eg3 : (close ("foo", 0) (open ("foo" , 0 ) (varen 0))) = (varen 0).
Proof.
  auto.
Defined.
Example eg4 : (close ("foo", 0) (open ("foo" , 0 ) (appe (varex ("foo", 0)) (varen 0)))) = (appe (varex ("foo", 0)) (varen 0)).
Proof.
  auto.
Defined.

Example eg5 : (open ("foo", 0) (close ("foo" , 0 ) (appe (varex ("foo", 0)) (varen 0)))) = (appe (varex ("foo", 0)) (varen 0)).
Proof.
  auto.
Defined.

Example eg6 : (open ("foo", 1) (close ("foo" , 1 ) (appe (varex ("foo", 0)) (varen 0)))) = (appe (varex ("foo", 0)) (varen 0)).
Proof.
  auto.
Defined.

Example eg7 : (close ("foo", 1) (open ("foo" , 1 ) (appe (varex ("foo", 0)) (varen 0)))) = (appe (varex ("foo", 0)) (varen 0)).
Proof.
  auto.
Defined.

Theorem left_identity : forall x e, (open x (close x e) = e).
Proof.
  induction e; simpl;
    repeat match goal with
      [ H: _ = _ |- _ ] => rewrite H
    end; try done.
  - (* var case *)
    case v.
    case x.
    intros.
    case: String.eqb_spec => Heqs; simpl.
    --
      case: Nat.eqb_spec => Heqn; simpl.
      ---
          by subst.
      ---
        case: Nat.ltb_spec; simpl; intro; subst;
          rewrite String.eqb_refl;
          case: Nat.leb_spec; try (intuition; omega).
          by rewrite (S_pred n0 n p).
    --
      rewrite <- String.eqb_neq in Heqs.
      by rewrite Heqs.
Qed.

Theorem right_identity : forall x e, (close x (open x e) = e).
Proof.
  (* Proof by induction on e. All cases, except the cases for variables, are
  trivial. *)
  induction e; simpl;
    repeat match goal with
      [ H: _ = _ |- _ ] => rewrite H
    end; try done.
  - (* free var case *)
    simpl.
    case v.
    case x.
    intros.
    case: String.eqb_spec; move => Heqs.
    --
    case: Nat.leb_spec; simpl; move => Heqn.
    ---
    rewrite Heqs.
    case String.eqb_spec; try intuition.
    case n eqn: Hn; auto.
    case: Nat.eqb_spec; try intuition.
    by omega.
    case: Nat.ltb_spec.
    auto.
    intro. by omega.
    ---
      subst.
      rewrite String.eqb_refl.
      assert ((n0 =? n)%nat = false).
      case: Nat.eqb_spec; try (intuition; omega).
      rewrite H.
      assert ((n <? n0) = false).
      case: Nat.ltb_spec; try intuition; omega.
      rewrite H0.
      done.
    --
      simpl.
      case: String.eqb_spec; try intuition.
  - (* bound var case *)
    case x.
    case n; try auto.
    --
      simpl.
    intros.
    rewrite String.eqb_refl.
    by rewrite Nat.eqb_refl.
Qed.

Fixpoint bind (e' : STLCE) (e : STLCE) : STLCE :=
  match e with
  | varex x => e
  | varen 0 => e'
  | varen n => varen (pred n)
  | lambdae A body => lambdae A (bind e' body)
  | appe e1 e2 => (appe (bind e' e1) (bind e' e2))
  end.


Fixpoint wk (e : STLCE) : STLCE :=
  match e with
  | varex x => e
  | varen n => varen (S n)
  | lambdae A body => lambdae A (wk body)
  | appe e1 e2 => (appe (wk e1) (wk e2))
  end.

SearchAbout ((?a -> ?b) -> (?b -> ?c) -> (?a -> ?c)).

Require Import Coq.Program.Basics.
Definition subst u x := compose (bind u) (close x).
Definition rename x y := compose (open y) (close x).
Definition shift x := compose (open x) wk.

Eval compute in (subst
                   (lambdae unit (appe (varen 0) (varex ("s" , 0))))
                   (("s" , 0))
                   (lambdae unit (appe (varen 0) (varex ("s" , 0))))).

Theorem bind_identity v e : (bind v (wk e)) = e.
Proof.
  (* By induction *)
  induction e; simpl;
    repeat match goal with
      [ H: _ = _ |- _ ] => rewrite H
    end; try done.
Qed.

Theorem rename_identity x e : (rename x x e) = e.
Proof.
  unfold rename.
  unfold compose.
  apply left_identity.
Qed.

Theorem subst_identity u x e : (subst u x (shift x e)) = e.
Proof.
  simpl.
  unfold subst.
  unfold shift.
  unfold compose.
  rewrite right_identity.
  apply bind_identity.
Qed.

Inductive STLCStep : STLCE -> STLCE -> Type :=
| stlc_beta : forall A e1 e2,
    STLCStep (appe (lambdae A e1) e2) (bind e2 e1).

Inductive STLCStepStar : STLCE -> STLCE -> Type :=
| stlc_step : forall e1 e2, STLCStep e1 e2 -> STLCStepStar e1 e2
| stlc_refl : forall e, STLCStepStar e e
| stlc_trans : forall e1 e2 e3, STLCStepStar e1 e2 -> STLCStepStar e2 e3 -> STLCStepStar e1 e3
| stlc_lambda_cong : forall A b b', STLCStepStar b b' -> STLCStepStar (lambdae A b) (lambdae A b')
| stlc_appe_cong1 : forall e1 e1' e2, STLCStepStar e1 e1' -> STLCStepStar (appe e1 e2) (appe e1' e2)
| stlc_appe_cong2 : forall e1 e2 e2', STLCStepStar e2 e2' -> STLCStepStar (appe e1 e2) (appe e1 e2').

(* Context should be a set; the names themselves implement shadowing.
   The process of adding a name to the set requires mapping open over the set.
   Removing a name from a set must map close over the set.

   Really, part of open/close should be abstracted out and *that* should be
   mapped over the set, and used in the definitions of open and close.

   This possibly could be done *once and forall*.
 *)
Inductive Dict_ref {A B : Type} : (A * B) -> list (A * B) -> Prop :=
| cons_ref : forall a b tl, Dict_ref (a , b) ((a , b) :: tl)
| rest_ref : forall a b c d tl, a <> c -> Dict_ref (a, b) tl -> Dict_ref (a, b) ((c, d) :: tl).

Inductive STLCType : list (Var * STLCA) -> STLCE -> STLCA -> Type :=
| T_Var : forall v A Γ, Dict_ref (v , A) Γ -> STLCType Γ (varex v) A
| T_Lambda : forall x A e Γ B, STLCType (cons (x , A) Γ) (open x e) B -> STLCType Γ (lambdae A e) (arr A B)
| T_App : forall e1 e2 A B Γ, STLCType Γ e1 (arr A B) -> STLCType Γ e2 A -> STLCType Γ (appe e1 e2) B.

SearchAbout list.

Lemma subst_pres' : forall Γ e1 A e2 B x, STLCType Γ e1 A -> STLCType (cons (x , A) Γ) e2 B -> STLCType Γ (subst e1 x e2) B.
Proof.
  move=>Γ e1 A e2 B x P1 P2.
  inversion P2.
  case (var_eqb_spec x v).
  intro.
  subst.
  unfold subst.
  unfold compose.
  assert ((close v (varex v)) = (varen 0)).
    simpl.
    case v.
    intros.
    rewrite String.eqb_refl.
    by rewrite Nat.eqb_refl.
  rewrite H0.
  simpl.
  assert (A = B).
    inversion P2.
    by inversion H3.
  by subst.
  unfold subst.
  unfold compose.
  simpl.
  case v eqn: Hv.
  case x.
  intros.
  case: String.eqb_spec.
  case: Nat.eqb_spec.
  intros.
  move: n1.
  by subst.
  intros.
  case (n0 <? n).
  simpl.
  move: P2.
  rewrite <- H1.
Abort.

(* Need the environment to reflect open/close:
  n0 < n ->
  STLCType (((s, n0), A) :: Γ) (varex (s, n)) B -> STLCType Γ (varex (s, Nat.pred n)) B

  or

  STLCType Γ e A -> x <> v -> STLCType (Γ-close x Γ) (subst e x (varex v)) A

  Or:

  STLCType Γ e A -> x <> v -> STLCType (Γ-close x Γ) (subst e x (varex v)) A

  Probably also need:

  STLCType Γ (lambda A e) (arr A B) -> STLCType ((x , A) :: (Γ-open x Γ)) (open x e) B
  ... or something
  *)
Lemma preservation : forall Γ e A e', (STLCType Γ e A) -> STLCStep e e' -> STLCType Γ e' A.
Proof.
  move=>Γ e A e' P1 P2.
  case P2 eqn: Hstep.
  unfold bind.

(* Fixpoint eval (e : STLCE) : STLCE :=
  match e with
  | (appe (lambdae _ e1) e2) => (eval (bind (eval e2) e1))
  | _ => e
  end. *)
