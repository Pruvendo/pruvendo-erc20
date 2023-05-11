Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.


Definition constructor_exec_sig (_initialAmount :  uint256) 
                                (_tokenName :  string) 
                                (_decimalUnits :  uint8) 
                                (_tokenSymbol :  string) (l : LedgerLRecord rec) :
                                {t | t = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l}.
  unfold constructor. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition constructor_exec_let (_initialAmount :  uint256) 
                                (_tokenName :  string) 
                                (_decimalUnits :  uint8) 
                                (_tokenSymbol :  string) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2 @constructor_exec_sig (constructor_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Defined.

Definition constructor_exec (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string) (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @constructor_exec_let (constructor_exec_let _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Defined.

Definition constructor_prf (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string) (l : LedgerLRecord rec) :
  constructor_exec _initialAmount _tokenName _decimalUnits _tokenSymbol l = 
  exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l.
  proof_of_2 constructor_exec constructor_exec_sig (constructor_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Defined.

