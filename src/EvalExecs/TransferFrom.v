Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Import EIP20.


Definition transferFrom_ls_template_exec_sig (_from :  address)
                                             (_to :  address)
                                             (_value :  uint256)
                                             (l : LedgerLRecord rec) :
           {t | t = exec_state (Uinterpreter (@transferFrom_ls_template rec def _ _ _ _ _from _to _value )) l}.
  unfold transferFrom_ls_template. unfold dynamicAssignL. unfold fromUReturnExpression.
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_ls_template_exec (_from :  address)
                                             (_to :  address)
                                             (_value :  uint256)
                                             (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @transferFrom_ls_template_exec_sig (transferFrom_ls_template_exec_sig _from _to _value l).
Defined.

(* Definition transferFrom_ls_template_exec (_from :  address)
                                         (_to :  address)
                                         (_value :  uint256)
                                         (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @transferFromTemplate_exec_let (transferFromTemplate_exec_let _from _to _value l).
Defined. *)

Definition transferFrom_ls_template_exec_prf (_from :  address)
                                             (_to :  address) 
                                             (_value :  uint256) 
                                             (l : LedgerLRecord rec) :
  transferFrom_ls_template_exec _from _to _value l = 
  exec_state (Uinterpreter (@transferFrom_ls_template rec def _ _ _ _ _from _to _value)) l.
  proof_of_2 transferFrom_ls_template_exec transferFrom_ls_template_exec_sig 
             (transferFrom_ls_template_exec_sig _from _to _value l).
Defined.


Definition transferFrom_ls_pre_payload_computed: 
                       forall (_from :  address)
                              (_to :  address) 
                              (_value :  uint256)
                              (l: LedgerLRecord rec), LedgerLRecord rec.
    (* {t: LedgerLRecord rec | t = transferFromTemplate_exec _from _to _value {$$ l with Ledger_LocalState := default $$}}. *)
Proof.
    intros.
    remember (transferFrom_ls_template_exec _from _to _value {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "transferFrom_ls_template_exec unfold" unfold transferFrom_ls_template_exec in Heql0. idtac.
    
    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def _ _ _ _ _ )) ?LL] => 
                                        remember LL
                              end
    end. idtac.

    time "transferFrom_ls_pre_payload_computed compute" vm_compute in Heql3. idtac.
    match goal with
    | Heql0: l3 = ?LL |- _ => exact LL
    end.
Defined.

Lemma transferFrom_ls_template_by_payload: 
                       forall (_from_value :  address)
                              (_to_value :  address) 
                              (_value_value :  uint256)
                              (l: LedgerLRecord rec), 
  let _from := local_left_field _ _ _ ("_from", 1%nat) in
  let _to := local_left_field _ _ _ ("_to", 1%nat) in
  let _value := local_left_field _ _ _ ("_value", 1%nat) in
  let _allowance := local_left_field _ _ _ ("allowance", 1%nat) in
  let _success := local_left_field _ _ _ ("success", 1%nat) in
  let l0 := transferFrom_ls_pre_payload_computed _from_value _to_value _value_value l in  

  transferFrom_ls_template_exec _from_value _to_value _value_value {$$ l with Ledger_LocalState := default $$} =
  exec_state (Uinterpreter (@transferFrom_ls_payload rec def _  _from _to _value _success _allowance)) l0.
Proof.
  intros.
  (* remember (transferFrom_ls_template_exec _from _to _value {$$ l with Ledger_LocalState := default $$}). *)

  destruct l. repeat destruct p.
  destruct v. repeat destruct p.
  destruct c. repeat destruct p. idtac.

  time "transferFrom_ls_template_exec unfold" unfold transferFrom_ls_template_exec. idtac.
    
  time "remember" match goal with
    | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember LL  
  end. idtac.

  time "transferFrom_ls_pre_payload_computed compute" vm_compute in Heql3. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a1                            
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a2
  
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a3                        
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a4
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a5
  end. idtac.

  assert (forall l, exec_state (sRReader (ULtoRValue u2)) l = l). 
  intros. 
  subst u2. auto.

  rewrite H.

  assert (forall X (x:X) (b: bool), 
    (if b then x else x) = x). intros; destruct b; auto.
  rewrite H0.

  assert (u = _from) by auto.
  assert (u0 = _to).
  subst u0 u. auto.
  assert (u1 = _value).
  subst u1 u0 u. auto.
  assert (u2 = _success ).
  subst u2 u1 u0 u. auto.
  assert (u3 = _allowance).
  subst u3 u2 u1 u0 u. auto.

  (* subst _from _to _value _allowance _success. *)
  rewrite H1, H2, H3, H4, H5.
  f_equal. auto. 
Qed.  

(* Definition transferFrom_ls_template_computed: 
                       forall (_from :  address)
                              (_to :  address) 
                              (_value :  uint256)
                              (l: LedgerLRecord rec), 
    {t: LedgerLRecord rec | t = transferFrom_ls_template_exec _from _to _value {$$ l with Ledger_LocalState := default $$}}. 
Proof.
    intros.
    remember (transferFrom_ls_template_exec _from _to _value {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "transferFrom_ls_template_exec unfold" unfold transferFrom_ls_template_exec in Heql0. idtac.
    
    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember LL
                              end
    end. idtac.

    time "transferFrom_ls_pre_payload_computed compute" vm_compute in Heql3. idtac.

    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a1
                              end
    end. idtac.

    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a2
                              end
    end. idtac.

    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a3
                              end
    end. idtac.

    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a4
                              end
    end. idtac.

    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                              | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a5
                              end
    end. idtac.

    assert (forall l, exec_state (sRReader (ULtoRValue u2)) l = l). 
    intros. 
    subst u2. auto.

    rewrite H in Heql0.

    assert (l0 = exec_state (UinterpreterUnf listInfinite (transferFrom_ls_payload rec def u u0 u1 u2 u3)) l3).
    rewrite Heql0.
    match goal with
    | |- context[if ?b then _ else _] => destruct b; auto
    end. (* clear Heql0 H. *)


    assert (u = local_left_field _ _ _ ("_from", 1%nat)) by auto.
    assert (u0 = local_left_field _ _ _ ("_to", 1%nat)).
    subst u0 u. auto.
    assert (u1 = local_left_field _ _ _ ("_value", 1%nat)).
    subst u1 u0 u. auto.
    assert (u2 = local_left_field _ _ _ ("success", 1%nat)).
    subst u2 u1 u0 u. auto.
    assert (u3 = local_left_field _ _ _ ("allowance", 1%nat)).
    subst u3 u2 u1 u0 u. auto.

    rewrite H1, H2, H3, H4, H5 in H0.
    rewrite Heql3 in H0.
    (* clear H1 H3 H H2 H4.     *)

    clear Heql0.
    match goal with
    | H: l0 = ?LL |- _ => refine (exist _ LL _)
    end. auto.

Defined. *)

(* payload *)

Definition transferFrom_ls_payload_exec_sig (_from : ULValue address) 
                                            (_to : ULValue address) 
                                            (_value : ULValue uint256)
                                            (_success: ULValue boolean)
                                            (_allowance : ULValue uint256) 
                                            (l : LedgerLRecord rec):
           {t | t = exec_state (Uinterpreter (@transferFrom_ls_payload rec def _  _from _to _value _success _allowance)) l}.
  unfold transferFrom_ls_payload. 
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_ls_payload_exec (_from : ULValue address) 
                                        (_to : ULValue address) 
                                        (_value : ULValue uint256)
                                        (_success: ULValue boolean) 
                                        (_allowance : ULValue uint256)
                                        (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @transferFrom_ls_payload_exec_sig (transferFrom_ls_payload_exec_sig  _from _to _value _success _allowance l).
Defined.

Definition transferFrom_ls_payload_prf (_from : ULValue address) 
                                       (_to : ULValue address) 
                                       (_value : ULValue uint256)
                                       (_success: ULValue boolean) 
                                       (_allowance : ULValue uint256)
                                       (l : LedgerLRecord rec) :
      transferFrom_ls_payload_exec _from _to _value  _success _allowance l = 
      exec_state (Uinterpreter (@transferFrom_ls_payload rec def _  _from _to _value _success _allowance)) l.
  proof_of_2 transferFrom_ls_payload_exec transferFrom_ls_payload_exec_sig (transferFrom_ls_payload_exec_sig _from _to _value _success _allowance l).
Defined.

Tactic Notation "lift_all" "in" hyp(H) := (repeat  
(rewrite exec_if_lift in H || 
 rewrite eval_if_lift in H || 
 rewrite toValue_if_lift in H )). 

Opaque Common.hmapFindWithDefault
       CommonInstances.addAdjustListPair
       N.add N.sub N.leb N.ltb N.eqb Z.eqb N.pow.

Definition transferFrom_ls_payload_exec_computed: forall (_from_value _to_value: address)
                                                         (_value_value : uint256)
                                                         (l: LedgerLRecord rec),
  let _from := local_left_field _ _ _ ("_from", 1%nat) in
  let _to := local_left_field _ _ _ ("_to", 1%nat) in
  let _value := local_left_field _ _ _ ("_value", 1%nat) in
  let _success := local_left_field _ _ _ ("success", 1%nat) in
  let _allowance := local_left_field _ _ _ ("allowance", 1%nat) in  
  let l0 := transferFrom_ls_pre_payload_computed _from_value _to_value _value_value l in
            {t: LedgerLRecord rec | t = transferFrom_ls_payload_exec _from _to _value  _success _allowance l0}.
Proof.        
    intros. 
    remember (transferFrom_ls_payload_exec  _from _to _value  _success _allowance l0).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "transferFrom_ls_payload_exec unfold" unfold transferFrom_ls_payload_exec in Heql1.
    time "transferFrom_ls_pre_payload_computed unfold" unfold transferFrom_ls_pre_payload_computed in Heql1.

    unfold xBoolIfElse in Heql1.
    unfold boolFunRec in Heql1. idtac.

    unfold transferFrom_ls_pre_payload_computed in l0.
    subst l0. idtac. 
    
    subst _from _to _value _success _allowance. idtac.

    time "lift" lift_all in Heql1. idtac.
    time "compute" compute in Heql1. idtac.
    time "buint" buint_all in Heql1. idtac.
    symmetry in Heql1. idtac.
     
    match goal with
    | Heql1: ?l = l1 |- _ => exact (@exist _ _ l Heql1)
    end.
Defined.



(* Definition transferFrom_exec_sig (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l}.
  unfold transferFrom. unfold dynamicAssignL.  unfold fromUReturnExpression.
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_exec_let (_from :  address)
                             (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined.

Definition transferFrom_exec (_from :  address)
                         (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @transferFrom_exec_let (transferFrom_exec_let _from _to _value l).
Defined.

Definition transferFrom_prf (_from :  address)
                         (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transferFrom_exec _from _to _value l = 
  exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l.
  proof_of_2 transferFrom_exec transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined. *)


Lemma remove_first_expression: forall X bb b`{XDefault X} (u1: UExpression X bb) (u2 u3: UExpression X b) (l: LedgerLRecord rec),
(forall l, exec_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) // {u2} //) l = exec_state (Uinterpreter // {u3} //) l) -> 
exec_state (Uinterpreter  (ledgerClass := LedgerLLedgerClass rec def) // {u1} ; {u2} //) l = exec_state (Uinterpreter // {u1} ; {u3} //) l.
Proof.
  intros.
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  (* erewrite <- E_err_arbitrary_false_P_helper. *)

  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  (* erewrite <- E_err_arbitrary_false_P_helper. *)
  match goal with
  | |- context [if ?b then _ else _] => destruct b
  end.
  - reflexivity.
  - eapply H0.
Qed.

Lemma remove_second_expression: forall X bb b`{XDefault X} (u1: UExpression X bb) (u2 u3: UExpression X b) (l: LedgerLRecord rec),
(forall l, exec_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) // {u2} //) l = 
           exec_state (Uinterpreter // {u3} //) l) -> 
(forall l, isError (eval_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) // {u2} //) l) = 
           isError (eval_state (Uinterpreter // {u3} //) l)) ->
exec_state (Uinterpreter  (ledgerClass := LedgerLLedgerClass rec def) // {u2} ; {u1} //) l = 
exec_state (Uinterpreter // {u3} ; {u1} //) l.
Proof.
  intros.
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  (* erewrite <- E_err_arbitrary_false_P_helper. *)

  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  (* erewrite <- E_err_arbitrary_false_P_helper. *)
  rewrite H1.
  match goal with
  | |- context [if ?b then _ else _] => remember b
  end.
  setoid_rewrite <- Heqb0. destruct b0.
  - eapply H0.
  - rewrite H0. reflexivity.
Qed.

Lemma remove_first_assigment: forall A X b`{XDefault X}`{LocalStateField mapping rec A}`{XDefault A}  
 (s:string) (f1 f2: ULValue A -> UExpression X b) (l: LedgerLRecord rec),
(forall ll lv (H: lv = eval_state (new_lvalue s) l), exec_state (Uinterpreter (f1 lv)) ll = exec_state (Uinterpreter (f2 lv)) ll) -> 
exec_state (Uinterpreter (dynamicAssignL s f1)) l = exec_state (Uinterpreter (dynamicAssignL s f2)) l.
Proof.
  intros.
  unfold dynamicAssignL.
  erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].  
  erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].    
  eapply H2. reflexivity.
Qed.

Lemma var_assigment_ass: forall A X b bb`{XDefault X}`{LocalStateField mapping rec A}`{XDefault A}  
 (s:string) (u: UExpression X b) (x: URValue A bb) (l: LedgerLRecord rec),
exec_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) (dynamicAssignL s (fun lv => // {lv} := {x} ; {u} //))) l =  
exec_state (Uinterpreter // {dynamicAssignL s (fun lv => // {lv} := {x} // ) } ; {u} // ) l.
Proof.
  intros.
  unfold dynamicAssignL.
  erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  symmetry.
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_dynamic_binding_eval_P_helper; [|reflexivity|reflexivity|reflexivity].

  reflexivity.
Qed.


Lemma double_assigment_exec': forall A`{LocalStateField mapping rec A}`{XDefault A}  
  (lv: ULValue A) (a a0: A) (l: LedgerLRecord rec),
exec_state (rpureLWriterN lv a0) (exec_state (rpureLWriterN lv a) l) =
exec_state (rpureLWriterN lv a0) l.
Admitted.

Lemma double_assigment_exec: forall A X b`{XDefault X}`{LocalStateField mapping rec A}`{XDefault A}  
 (u: UExpression X b) (lv: ULValue A) (x: URValue A false) (y: URValue A false) (l: LedgerLRecord rec),
exec_state (sRReader x) l = l -> 
(forall l, exec_state (sRReader y) l = l) -> 
(forall a, eval_state (sRReader y) (exec_state (rpureLWriterN lv a) l) = eval_state (sRReader y) l) ->
exec_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) 
                         // {lv} := {x} ; {lv} := {y} ; {u} // ) l =
exec_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) 
                         // {lv} := {y} ; {u} // ) l.
Proof.
  intros.
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_err_arbitrary_false_P_helper.
  erewrite <- E_assign_exec_false_P_helper with (r:=x); [|reflexivity|reflexivity|reflexivity].
  rewrite H2.
  remember (toValue (eval_state (sRReader x) l)).
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_strict_bind_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- ?E_err_arbitrary_false_P_helper.
  erewrite <- E_assign_exec_false_P_helper with (r:=y); [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_assign_exec_false_P_helper with (r:=y); [|reflexivity|reflexivity|reflexivity].
  remember (toValue (eval_state (sRReader y) l)).
  rewrite ?H3.

  f_equal.
  rewrite H4. rewrite <- Heqa0.
  erewrite double_assigment_exec' with (A:=A); auto.
Qed.

Lemma double_assigment_eval: forall A X b`{XDefault X}`{LocalStateField mapping rec A}`{XDefault A}  
 (u: UExpression X b) (lv: ULValue A) (x: URValue A false) (y: URValue A false) (l: LedgerLRecord rec),
exec_state (sRReader x) l = l -> 
(forall l, exec_state (sRReader y) l = l) -> 
(forall a, eval_state (sRReader y) (exec_state (rpureLWriterN lv a) l) = eval_state (sRReader y) l) ->
eval_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) 
                         // {lv} := {x} ; {lv} := {y} ; {u} // ) l =
eval_state (Uinterpreter (ledgerClass := LedgerLLedgerClass rec def) 
                         // {lv} := {y} ; {u} // ) l.
Proof.                         
  intros.
  erewrite <- E_strict_bind_eval_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_assign_eval_P_helper; [|reflexivity].
  remember (eval_state (sRReader x) l).
  dependent destruction c.

  erewrite <- E_assign_exec_false_P_helper with (r:=x); [|reflexivity|reflexivity|reflexivity].
  rewrite H2.
  remember (toValue (eval_state (sRReader x) l)).

  erewrite <- E_strict_bind_eval_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_assign_eval_P_helper; [|reflexivity].
  symmetry.
  erewrite <- E_strict_bind_eval_P_helper; [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_assign_eval_P_helper; [|reflexivity].
  rewrite H4.
  remember (eval_state (sRReader y) l).
  dependent destruction c.

  erewrite <- E_assign_exec_false_P_helper with (r:=y); [|reflexivity|reflexivity|reflexivity].
  erewrite <- E_assign_exec_false_P_helper with (r:=y); [|reflexivity|reflexivity|reflexivity].
  remember (toValue (eval_state (sRReader y) l)).
  rewrite ?H3. rewrite H4. 
  change (toValue (ControlValue false a)) with a.
  erewrite double_assigment_exec' with (A:=A); auto.
  replace a2 with a.
  remember (eval_state (UinterpreterUnf listInfinite u) (exec_state (rpureLWriterN lv a) l)).
  dependent destruction c; auto.

  remember (eval_state (sRReader y) l).
  dependent destruction c.
  inversion Heqc0. auto.
Qed.


Lemma transferFrom_ls_template_exec_correct_helper: forall l l' (u: URValue _ false),
    l.(Ledger_MainState) = l'.(Ledger_MainState) ->
    l.(Ledger_VMState) = l'.(Ledger_VMState) ->
    eval_state (sRReader u) l = eval_state (sRReader u) l' ->
    (forall l, (exec_state (sRReader u) l).(Ledger_MainState) = l.(Ledger_MainState)) ->
    eval_state (sRReader (URIndex \\ msg->sender \\ (URIndex u (allowed_right rec def)))) l = 
    eval_state (sRReader (URIndex \\ msg->sender \\ (URIndex u (allowed_right rec def)))) l'.
Proof.
  intros.
  destruct l. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p. 

  destruct l'. repeat destruct p.
  destruct c. repeat destruct p.
  destruct v. repeat destruct p.

  compute in H. compute in H0.
  inversion H. subst x x0 x1 x2 x3 x4. 
  inversion H0. subst x5 x6 x7 x8 x9 a x10 x11 a0 t t0 x12 x13 t1 x14 x15 l1 x16.
  clear H H0.

  assert (forall X (c1: ControlResult X false) c2,
          toValue c1 = toValue c2 -> c1 = c2 ).
  -
    intros. 
    dependent destruction c2; dependent destruction c3.
    compute in H. congruence.
  -
    apply H.
    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    symmetry.
    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    
    unfold msg_sender. unfold wrapURValue.
    unfold SML_NG32.wrapURValue.
    erewrite <- ?R_state_exec_P_helper.

    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    symmetry.
    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    rewrite H1.

    f_equal. f_equal. f_equal.

    match goal with
    | |- context [eval_state _ (exec_state _ ?l) = 
                  eval_state _ (exec_state _ ?l1)]
        => remember l; remember l1
    end.

    pose proof (H2 x).
    pose proof (H2 x0).
    remember (exec_state (sRReader u) x).
    remember (exec_state (sRReader u) x0).
    setoid_rewrite <- Heqx1 in H0.
    setoid_rewrite <- Heqx2 in H3.
    setoid_rewrite <- Heqx1.
    setoid_rewrite <- Heqx2.
        
    destruct x1. repeat destruct p.
    destruct c. repeat destruct p.
    destruct v. repeat destruct p. 

    destruct x2. repeat destruct p.
    destruct c. repeat destruct p.
    destruct v. repeat destruct p.

    subst x0 x.
    compute in H0, H3.

    inversion H0.
    subst x1 x3 x4 x5 x6 x7.

    inversion H3.
    subst x2 x38 x39 x40 x41 x42.
    auto.
Qed.


Lemma transferFrom_ls_template_exec_correct: forall (_from :  address)
                                                    (_to :  address) 
                                                    (_value :  uint256) 
                                                    (l : LedgerLRecord rec),
      exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l = 
      exec_state (Uinterpreter (@transferFrom_ls_template rec def _ _ _ _  _from _to _value)) l.
Proof.
  intros.
  unfold transferFrom.
  unfold transferFrom_ls_template.
  unfold transferFrom_ls_payload.
  unfold fromUReturnExpression.

  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.
  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.
  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.
  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.

  unfold dynamicAssignL.
  
  match goal with
  | |- context [@DynamicBinding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  ?f] => remember f
  end.
  symmetry.
  match goal with
  | |- context [@DynamicBinding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  ?f] => remember f
  end.

  match goal with
  | |- context [ // {?u1} ; {?u2} //  ] => remember u1; remember u2
  end.
  symmetry.
  match goal with
  | |- context [ // {?u1} ; {?u2} //  ] => remember u1
  end.

  apply remove_second_expression with  (u1:=u2) (u2:=u3) (u3:=u1); intros.
  
  all: subst u3 u1 u u0.
  1: erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  1: erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  2: erewrite <- E_dynamic_binding_err_P_helper; [|reflexivity|reflexivity|reflexivity].
  2: erewrite <- E_dynamic_binding_err_P_helper; [|reflexivity|reflexivity|reflexivity].
  
  all: remember (eval_state (SML_NG32.new_lvalue "allowance") l4).  
  all: symmetry.
  all: match goal with
  | |- context [ // {?x} ; {?y} := {?a} ; {?z} // ] => remember a; remember z
  end.
  all: remember (exec_state (SML_NG32.new_lvalue "allowance") l4).
  
  1: apply double_assigment_exec with 
           (lv := u) 
           (u := u1) (y:=u0) (l:=l5).
  6: f_equal; apply double_assigment_eval with 
           (lv := u) 
           (u := u1) (y:=u0) (l:=l5).

  1,6: refine LocalStateField0.
  1,5: refine ubint_default.
  1,4: auto.
  1,3:  ( intros ; subst u0 lv;
         destruct l6 ; repeat destruct p ;
         destruct c ; repeat destruct p ;
         destruct v ; repeat destruct p ; auto ).
  all:  (intros; subst u u0 lv;
    remember ((eval_state (new_lvalue "_from") l1)) ;
    apply transferFrom_ls_template_exec_correct_helper ).
  1,5: (destruct l5 ; repeat destruct p ;
        destruct c ; repeat destruct p ;
        destruct v ; repeat destruct p ; auto ).
  1,4: (destruct l5 ; repeat destruct p ;
        destruct c ; repeat destruct p ;
        destruct v ; repeat destruct p ; auto).
  1,3:  (subst u;
    destruct l5;  repeat destruct p;
    destruct c; repeat destruct p;
    destruct v; repeat destruct p). 
  1,2:  (
    destruct l1; repeat destruct p;
    destruct c; repeat destruct p;
    destruct v; repeat destruct p).         

  1,2:  (
    destruct l4; repeat destruct p;
    destruct c; repeat destruct p;
    destruct v; repeat destruct p; auto).

    Opaque Common._hmapFindWithDefault _addAdjustListPair.
   1,2: (compute;
    destruct l1 ; destruct l12;
    destruct l12 ; destruct l5 ;
    destruct l12 ; destruct l12 ; reflexivity ).

    Transparent Common._hmapFindWithDefault _addAdjustListPair.
    1,2: (subst u;
    destruct l5; repeat destruct p;
    destruct c; repeat destruct p;
    destruct v; repeat destruct p;  auto ) .
Qed.

Definition transferFrom_exec_computed: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
  {t: LedgerLRecord rec | t = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value))  {$$ l with Ledger_LocalState := default $$}}.
  intros.
  remember (transferFrom_ls_payload_exec_computed _from _to _value l ).  
  unfold transferFrom_ls_payload_exec_computed in Heqs.
  refine (exist _ (proj1_sig s) _).
  rewrite transferFrom_ls_template_exec_correct.
  rewrite <- transferFrom_ls_template_exec_prf.
  rewrite transferFrom_ls_template_by_payload.
  rewrite <- transferFrom_ls_payload_prf.
  apply (proj2_sig).
Defined.  


Print transferFrom_exec_computed.





(* Definition transferFrom_exec_computed: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
                            {t: LedgerLRecord rec | t = transferFrom_exec _from _to _value {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (transferFrom_exec _from _to _value {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  idtac.

    unfold transferFrom_exec in Heql0. idtac.    

    unfold xBoolIfElse in Heql0.
    unfold boolFunRec in Heql0.

    time "lift1" lift_all in Heql0.         
    time "compute1" compute in Heql0.  
    time "buint1" buint_all in Heql0.
    symmetry in Heql0. idtac.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined. *)





(*eval*)

(* Definition transferFrom_eval_sig (_from :  address) (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = eval_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l}.
  unfold transferFrom. unfold dynamicAssignL.
  unfold fromUReturnExpression.  
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_eval_let (_from :  address) (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : ControlResult bool true.
  let_term_of_2_fast @transferFrom_eval_sig (transferFrom_eval_sig _from _to _value l).
Defined.

Definition transferFrom_eval (_from :  address) (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : ControlResult bool true.
  flat_term_of_2 @transferFrom_eval_let (transferFrom_eval_let _from _to _value l).
Defined.

Definition transferFrom_eval_prf (_from :  address) (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transferFrom_eval _from _to _value l = 
  eval_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l.
  proof_of_2 transferFrom_eval transferFrom_eval_sig (transferFrom_eval_sig _from _to _value l).
Defined. *)



(* template left *)

(* Definition transferFromTemplate_exec_sig1 
                                 (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@transferFromTemplate_left rec def _ _ _ _ false (URScalar _from) false (URScalar _to) false (URScalar _value) bool )) l}.
  unfold transferFromTemplate_left.
  unfold wrapULExpressionL.
  unfold wrapULExpression.
  unfold ursus_call_with_argsL.

  match goal with
  | |- context [@ursus_call_with_args ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20] =>
            remember (@ursus_call_with_args a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20)
  end.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_1 in u.
  change (transferFromTemplate rec def) with (fun (_from _to : address) (_value : uint256) => transferFromTemplate rec def _from _to _value) in Hequ.
  Opaque transferFromTemplate.
  
  simpl in Hequ.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_4 in Hequ.  
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_4 in Hequ.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_5 in Hequ.
  unfold ursus_call_with_rargs0 in Hequ.
  simpl in Hequ.
  unfold simple_state_bind,  simple_state_unit in Hequ.
  unfold simple_state_run in Hequ.
  unfold compose in Hequ.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_7 in Hequ.
  unfold sRReader in Hequ.
  simpl in Hequ.

  change Datatypes.list with XList.

  auto_build_P listInfinite.
  all: subst u.  
  1: refine (exist _ (exec_state (UinterpreterUnf listInfinite (transferFromTemplate rec def _from _to _value)) l) _).
  2: refine (exist _ (eval_state (UinterpreterUnf listInfinite (transferFromTemplate rec def _from _to _value)) l) _).

  all: remember (UinterpreterUnf listInfinite (transferFromTemplate rec def _from _to _value)) as ll.
  all: destruct ll.
  1: unfold exec_state.
  2: unfold eval_state.
  all: simpl.
  all: remember (x l) as xx.
  all: destruct xx. 
  all: simpl. 
  1: reflexivity.
  dependent destruction c; reflexivity.
Defined.



Definition transferFromTemplate_exec_sig2 
                                 (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@transferFromTemplate_left rec def _ _ _ _ false (URScalar _from) false (URScalar _to) false (URScalar _value) bool )) l}.
remember (proj1_sig (transferFromTemplate_exec_sig1 _from _to _value l)).
pose proof (proj2_sig (transferFromTemplate_exec_sig1 _from _to _value l)).
unfold transferFromTemplate_exec_sig1 in Heql0, H.
setoid_rewrite <- Heql0 in H.
simpl in Heql0.

symmetry in Heql0.

match goal with 
| Heql0: ?L = l0 |- _ => refine (exist _ L _)
end.
rewrite Heql0.
assumption.
Defined.


Definition transferFromTemplate_exec_sig3
                                 (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@transferFromTemplate_left rec def _ _ _ _ false (URScalar _from) false (URScalar _to) false (URScalar _value) bool )) l}.
remember (proj1_sig (transferFromTemplate_exec_sig2 _from _to _value l)).
pose proof (proj2_sig (transferFromTemplate_exec_sig2 _from _to _value l)).
unfold transferFromTemplate_exec_sig2 in Heql0, H.
setoid_rewrite <- Heql0 in H.
simpl in Heql0.
Admitted.


Transparent transferFromTemplate. *)