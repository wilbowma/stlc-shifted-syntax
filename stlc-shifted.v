Require Import Strings.String.
Require Import Strings.Ascii.

Open Scope string_scope.

Require Import Bool.
Require Import Omega.
Require Import Nat.

Require Import ssreflect.

Definition Var := (string * nat)%type.

Inductive STLCA : Type :=
  | unit : STLCA
  | arr (A : STLCA) (b : STLCA) : STLCA.

Inductive STLCE : Type :=
| varex (v : Var) : STLCE
| varen (n : nat) : STLCE
| lambdae (A : STLCA) (body : STLCE) : STLCE
| appe (e1 : STLCE) (e2 : STLCE) : STLCE.

Fixpoint var_eqb (x1 x2 : Var) : bool :=
  match x1 with
  | (s1, n1) => match x2 with
                | (s2, n2) => (if (s1 =? s2)%string then
                                 if (n1 =? n2)%nat then
                                   true
                                 else false
                              else false)
                end
  end.

Fixpoint open (x : Var) (e : STLCE) : STLCE :=
  match e with
  | varen 0 => varex x
  | varen (S n) => varen n
  | varex (s , n) => (match x with
                      | (s' , n') => (if (s =? s') then
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
                         | (s' , n') => (if (s =? s') then
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