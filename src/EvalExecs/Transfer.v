Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.

(* exec *)

Definition transfer_exec_sig (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = exec_state (Uinterpreter (@transfer rec def _ _ _ _  _to _value)) l}.
  unfold transfer. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition transfer_exec_let (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2 @transfer_exec_sig (transfer_exec_sig _to _value l).
Defined.

Definition transfer_exec (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @transfer_exec_let (transfer_exec_let _to _value l).
Defined.

Definition transfer_exec_prf (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transfer_exec _to _value l = 
  exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l.
  proof_of_2 transfer_exec transfer_exec_sig (transfer_exec_sig _to _value l).
Defined.

(* eval *)

Definition transfer_eval_sig (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = eval_state (Uinterpreter (@transfer rec def _ _ _ _  _to _value)) l}.
  unfold transfer. unfold dynamicAssignL.
  unfold fromUReturnExpression.  
  repeat auto_build_P listInfinite.
Defined.

Definition transfer_eval_let (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : ControlResult bool true.
  let_term_of_2 @transfer_eval_sig (transfer_eval_sig _to _value l).
Defined.

Definition transfer_eval (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : ControlResult bool true.
  flat_term_of_2 @transfer_eval_let (transfer_eval_let _to _value l).
Defined.

Definition transfer_eval_prf (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transfer_eval _to _value l = 
  eval_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l.
  proof_of_2 transfer_eval transfer_eval_sig (transfer_eval_sig _to _value l).
Defined.