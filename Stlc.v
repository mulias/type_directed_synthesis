(** * Stlc: The Simply Typed Lambda-Calculus *)

Add LoadPath "~/src/stlc_coq/".
Require Export SfLib.

Module STLC.

(* Types *)
Inductive ty : Type := 
  | TBool  : ty
  | TNat   : ty
  | TArrow : ty -> ty -> ty.


(* Terms *)
Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tiszero : tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif" ].


(* Values *)
Inductive avalue : tm -> Prop := 
  | av_abs : forall x T t, avalue (tabs x T t).

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := avalue t \/ bvalue t \/ nvalue t.

Hint Constructors avalue bvalue nvalue.
Hint Unfold value.  
Hint Unfold extend.


(* Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | tzero =>
      tzero
  | tsucc n =>
     tsucc ([x:=s] n)
  | tiszero n =>
      tiszero ([x:=s] n)
  end

where "'[' x ':=' s ']' t" := (subst x s t).


(* Small-Step Semantics *)
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* final substitution *)
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  (* reduce the left side *)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  (* reduce the right side *)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  (* return first clause if true *)
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  (* return second clause if false *)
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  (* reduce test to a ttrue or tfalse *)
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  (* step body of Succ *)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  (* iszero(O) is true *)
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  (* iszero(S(n)) is false *)
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  (* step body of iszero *)
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.


(* Typing, Contexts *)
Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->                       
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.

Definition context := partial_map ty.


(* Generation Relation *)
Reserved Notation "Gamma '|-' T '~>' t" (at level 40).
    
Inductive gens_term : context -> ty -> tm -> Prop :=
  | G_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- T ~> tvar x
  | G_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- T12 ~> t12 -> 
      Gamma |- TArrow T11 T12 ~> tabs x T11 t12
  | G_App : forall T11 T12 Gamma t1 t2,
      Gamma |- TArrow T11 T12 ~> t1 ->
      Gamma |- T11 ~> t2 ->
      Gamma |- T12 ~> tapp t1 t2
  | G_True : forall Gamma,
       Gamma |- TBool ~> ttrue
  | G_False : forall Gamma,
       Gamma |- TBool ~> tfalse
  | G_If : forall t1 t2 t3 T Gamma,
       Gamma |- TBool ~> t1 ->
       Gamma |- T ~> t2 ->
       Gamma |- T ~> t3 ->
       Gamma |- T ~> tif t1 t2 t3
  | G_Zero : forall Gamma,
       Gamma |- TNat ~> tzero
  | G_Succ : forall t1 Gamma,
       Gamma |- TNat ~> t1 ->
       Gamma |- TNat ~> tsucc t1
  | G_Iszero : forall t1 Gamma,
       Gamma |- TNat ~> t1 ->
       Gamma |- TBool ~> tiszero t1

where "Gamma '|-' T '~>' t" := (gens_term Gamma T t).

Tactic Notation "gens_term_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "G_Var" | Case_aux c "G_Abs" 
  | Case_aux c "G_App" | Case_aux c "G_True" 
  | Case_aux c "G_False" | Case_aux c "G_If" ].

Hint Constructors gens_term.

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Example gen_example_1 :
  empty |- TArrow TBool TBool ~> tabs x TBool (tvar x).
Proof.
  apply G_Abs. apply G_Var. reflexivity.  Qed.

(* (bool->((bool->bool)->bool)) ~> (\x:bool.(\y:bool->bool.(y(y x)))) *)
Example typing_example_2 :
  empty |-
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)) ~>
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))).
Proof with auto using extend_eq.
  apply G_Abs. apply G_Abs. eapply G_App. apply G_Var...
  eapply G_App. apply G_Var...
  apply G_Var...
Qed.

(* thesis page 14 example *)
Example typing_example_3 :
  empty |-
    (TArrow TBool TBool) ~>
    (tapp (tabs x (TArrow TBool TBool) (tvar x)) (tabs y TBool ttrue)).
Proof with auto using extend_eq.
  eapply G_App. apply G_Abs. apply G_Var...
  apply G_Abs. apply G_True.
Qed.

(* Nat ~> S(S(S(O))) *)
Example typing_example_4 :
  empty |-
    TNat ~>
    tsucc (tsucc (tsucc tzero)).
Proof with auto using extend_eq.
  auto.
Qed.

(* Nat ~> (\x:nat.S(x)) O *)
Example typing_example_5 :
  empty |-
    TNat ~>
    tapp (tabs x TNat (tsucc (tvar x))) (tsucc tzero).
Proof with auto using extend_eq.
  eapply G_App. apply G_Abs. apply G_Succ. apply G_Var...
  apply G_Succ. apply G_Zero.
Qed.


End STLC.

