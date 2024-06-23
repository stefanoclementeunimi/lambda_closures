Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Require Import Unicode.Utf8.
From Hammer Require Import Hammer.

(*STLC
As terms, we will consider a single constant term UNIT, along with the usual ones: variables, abstractions
and applications.
As types, we will consider the arrow and the UNIT type.
*)

Inductive ty : Type :=
  | Ty_Unit  : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_ut    : tm. 

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Unit'" := Ty_Unit (in custom stlc at level 0).

Notation "'unit'" := tm_ut (in custom stlc at level 0).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.


(*Co-inductive definition of environment and values: values are the unit constant
and closures; environments are lists of variables bound to values*)

Inductive env: Type :=
| empty: env
| cons: string -> val -> env -> env
with val: Type :=
| unit: val
| closure: env -> tm -> val.


(*Typing context: our type environments are defined as lists of variables bound to types*)

Inductive tenv: Type :=
| tEmpty: tenv
| tCons: string -> ty -> tenv -> tenv.

Open Scope string_scope.

(*Lookup (relational form) & update - extension - of our environment*)

Inductive env_lookup: env -> string -> val -> Prop :=
| here x w rest: env_lookup (cons x w rest) x w
| there x y w ww eta: env_lookup eta x w -> env_lookup (cons y ww eta) x w.

Definition env_update (e: env)(x:string)(v: val): env := cons x v e.


(*Evaluation of terms*)

Inductive evaluate: env -> tm -> val -> Prop:=
| eval_unit: forall e: env, evaluate e <{unit}> unit
| eval_abs: forall  e x T2 t1, evaluate e <{\x:T2, t1}> (closure e <{\x:T2, t1}>)
| eval_var: forall e x v, env_lookup e x v -> evaluate e x v
| eval_app: forall e e' x t1 t2 t3 T2 v v',
            evaluate e t2 (closure e' <{\x: T2, t1}>) ->
            evaluate e t3 v' ->
            evaluate(env_update e' x  v') t1 v -> 
            evaluate e <{t2 t3}> v.

(*Lookup (relational form) & update - extension - of our typing context*) 
Inductive tenv_lookup: tenv -> string -> ty -> Prop :=
| t_here x w rest: tenv_lookup (tCons x w rest) x w
| t_there x y w ww eta: tenv_lookup eta x w -> tenv_lookup (tCons y ww eta) x w.


Definition tenv_update(e: tenv)(x:string)(t: ty): tenv := tCons x t e.


(*Synctactic typing relation for terms *)

Inductive has_type: tenv -> tm -> ty -> Prop :=
| t_Unit: forall context, has_type context <{unit}> Ty_Unit
| t_Var: forall context x T1, tenv_lookup context x T1 -> has_type context x T1
| t_Abs: forall context x (T1: ty) T2 t1,
         has_type (tenv_update context x T2) t1 T1 -> 
         has_type context <{\x:T2, t1}> (Ty_Arrow T2 T1)
| t_App: forall context T1 T2 t1 t2,
         has_type context t1 (Ty_Arrow T2 T1) -> 
         has_type context t2 T2 -> has_type context <{t1 t2}> T1.

(*Co-inductive (synctactic) typing relation for environments & val*)

Inductive hasty_env: env -> tenv -> Prop:=
| type_empty: hasty_env empty tEmpty
| type_cons: forall e ctx x v t, 
             hasty_env e ctx -> 
             has_ty v t ->
             hasty_env (env_update e x v)(tenv_update ctx x t)   
with has_ty: val -> ty -> Prop:=
| type_unit: has_ty unit Ty_Unit
| type_closure: forall e ctx x T T2 t1, 
                has_type ctx <{\x: T2, t1}> T ->
                hasty_env e ctx-> 
                has_ty (closure e <{\x: T2, t1}>) T.

(*The synctactic typing for the values so far defined is consistent*)

Lemma eta_gamma: forall eta x v TE T,  env_lookup eta x v
-> tenv_lookup TE x T -> 
hasty_env eta TE -> has_ty v T.
Proof. 
intros.
induction H1. 
- sauto lq: on.
- inversion H; subst.
Admitted. 


Theorem consistency: forall Ks M W TE T,
  evaluate Ks M W -> hasty_env Ks TE -> has_type TE M T -> has_ty W T.
Proof.
  intros.
  generalize dependent TE.
  generalize dependent T.
  induction H; intros.
  - sauto lq: on .
  - sauto lq: on .
  - rename e into eta. inversion_clear H1; subst. eapply eta_gamma; eauto.
  - inversion_clear H3; subst. assert (H2' := H2). 
    apply IHevaluate1 with(T:=<{ T0 -> T }>) in H2; try(assumption).
    apply IHevaluate2 with (T:=T0) in H2'; try(assumption).
    inversion_clear H2; subst. inversion_clear H3; subst. 
    apply type_cons with (x:=x0)(t:=T0)(v:=v') in H6; try(assumption).
    eapply IHevaluate3. eauto. assumption. 
Qed.




(*Semantic Types*)

Fixpoint R (T: ty)(w: val) :Prop :=
    (match T with
 | Ty_Unit  => True
 | Ty_Arrow T1 T2 => 
     ( match w with
       | closure eta <{ \ x : T1', t1 }>  
            => (T1 = T1' /\ forall a, R T1 a  ->  exists b,  
                evaluate (env_update eta x a) t1 b /\  R T2 b)
       | _ => False
       end)
    end).

Print R.

(*Semantic typing for environments*)

Definition REG (gamma : tenv) (eta : env) :=
forall (x : string) (T : ty), has_type gamma x T -> exists a, 
    env_lookup eta x a /\ R T a.

(*Semantic typing for terms *)

Definition Valid (gamma :tenv) (t : tm)  (T : ty) : Prop :=
forall eta, REG gamma eta -> exists a, evaluate eta t a /\ R T a.

(*Extension lemma for semantically typed environments*)

Lemma extend: forall gamma eta T a x, REG gamma eta -> R T a 
-> REG (tenv_update gamma x T)(env_update eta x a).
Proof.
intros. destruct gamma; destruct eta; unfold REG in  *; sauto lq:on.  
Qed.

(*Well-typed terms are semantically typed*)

Lemma fundamental: forall gamma t T, has_type gamma t T -> Valid gamma t T.
Proof.
intros. induction H. 
(*Case UNIT*)
- sauto.
 (*Case VAR*) 
- unfold Valid. intros. unfold REG in H0.  apply t_Var in H. apply H0 in H.
  inversion H. destruct H1. exists x1. sauto.
(*case ABS + inductive hyp*) 
- unfold Valid. unfold REG. intros.     
exists (closure eta <{\ x0: T2, t1}>). sauto use: extend.
(*case app + inductive hyp*)
- unfold Valid in *. intros. assert (H1':=H1). apply IHhas_type1 in H1. 
  apply IHhas_type2 in H1'. sauto.
Qed.


(*Totality of evaluation: the evaluation of any (well-typed) term is well-defined*)
Corollary total: forall t T, has_type tEmpty t T -> exists a, evaluate empty t a.
Proof.
intros. apply fundamental in H. unfold Valid in H. destruct H with empty. 
- unfold REG. intros. exists unit. sauto.
- exists x0. destruct H0. assumption.
Qed.


