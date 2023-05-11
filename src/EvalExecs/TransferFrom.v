Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.

(* exec *)

Definition transferFrom_exec_sig (_from :  address)
                             (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l}.
  unfold transferFrom. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_exec_let (_from :  address)
                             (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2 @transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
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
Defined.

(* Definition transferFrom_let_prf (_from :  address)
                         (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transferFrom_exec_let _from _to _value l = 
  exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l.
  proof_of_2 transferFrom_exec_let transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined. *)

Definition transferFrom_eval_sig (_from :  address) (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = eval_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l}.
  unfold transferFrom. unfold dynamicAssignL.
  unfold fromUReturnExpression.  
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_eval_let (_from :  address) (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : ControlResult bool true.
  let_term_of_2 @transferFrom_eval_sig (transferFrom_eval_sig _from _to _value l).
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
Defined.
