(** * Stlc: The Simply Typed Lambda-Calculus *)

Add LoadPath "~/src/stlc_coq/".
Require Export SfLib.

Module STLC.

(* Types *)
Inductive ty : Type := 
  | TBool  : ty 
  | TArrow : ty -> ty -> ty.

(* Terms *)
Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

(* Values *)
Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse.

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
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Small-Step Semantics *)
(*

value v2
----------------------------                                   (ST_AppAbs)
(\x:T.t12) v2 ==> [x:=v2]t12

t1 ==> t1'
----------------                                               (ST_App1)
t1 t2 ==> t1' t2

value v1
t2 ==> t2'
----------------                                               (ST_App2)
v1 t2 ==> v1 t2'

--------------------------------                               (ST_IfTrue)
(if true then t1 else t2) ==> t1

---------------------------------                              (ST_IfFalse)
(if false then t1 else t2) ==> t2

t1 ==> t1'
----------------------------------------------------           (ST_If)
(if t1 then t2 else t3) ==> (if t1' then t2 else t3)


---------------------------                                    (ST_EguessVar)
*)

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

where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).




(* Testing *)

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif" ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(* [idB = \x:Bool. x] *)
Notation idB := 
  (tabs x TBool (tvar x)).

(* [idBB = \x:Bool->Bool. x] *)
Notation idBB := 
  (tabs x (TArrow TBool TBool) (tvar x)).

(* [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)
Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool) 
                      (TArrow TBool TBool)) 
    (tvar x)).

(* [k = \x:Bool. \y:Bool. x] *)
Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(* [notB = \x:Bool. if x then false else true] *)
Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

Hint Constructors value.

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

(** Example:
    ((\x:Bool->Bool. x) (\x:Bool. x)) ==>* (\x:Bool. x)
i.e.
    (idBB idB) ==>* idB
*)

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.  

(** Example:
((\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))) 
      ==>* (\x:Bool. x)
i.e.
  (idBB (idBB idB)) ==>* idB.
*)

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed. 

(** Example:
((\x:Bool->Bool. x) (\x:Bool. if x then false
                              else true)) true)
      ==>* false
i.e.
  ((idBB notB) ttrue) ==>* tfalse.
*)

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed. 

(** Example:
((\x:Bool -> Bool. x) ((\x:Bool. if x then false
                               else true) true))
      ==>* false
i.e.
  (idBB (notB ttrue)) ==>* tfalse.
*)

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_IfTrue. 
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed. 


(** A more automatic proof *)

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof. normalize.  Qed.  

(** Again, we can use the [normalize] tactic from above to simplify
    the proof. *)

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  normalize.
Qed. 

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.  

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.  

(** **** Exercise: 2 stars (step_example3)  *)  
(** Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  normalize. Qed.

End STLC.

