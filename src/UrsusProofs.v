Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Import EIP20.

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