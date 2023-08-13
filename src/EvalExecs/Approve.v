Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.


Definition approve_exec_sig (_spender :  address) (_value :  uint256) (l : LedgerLRecord rec) :
                                {t | t = exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) l}.
  unfold approve. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition approve_exec_let (_spender :  address) (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @approve_exec_sig (approve_exec_sig _spender _value l).
Defined.

Definition approve_exec (_spender :  address) (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @approve_exec_let (approve_exec_let _spender _value l).
Defined.

Definition approve_prf (_spender :  address) (_value :  uint256) (l : LedgerLRecord rec) :
  approve_exec _spender _value l = 
  exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) l.
  proof_of_2 approve_exec approve_exec_sig (approve_exec_sig _spender _value l).
Defined.

