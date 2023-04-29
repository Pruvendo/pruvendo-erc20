Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

#[global, program]
Instance listInfinite : listInfiniteFunRec_gen XList.
Next Obligation.
(* TODO: we need to analyze all while/for cycles
   and find upper bound for number of iterations *)
exact (repeat PhantomPoint 0).
Defined.

Notation rec := LocalStateLRecord.

Definition computed : LocalStateLRecord := Eval vm_compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 

Definition VMStateDefault : VMStateLRecord  := Eval vm_compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval vm_compute in default. 

Elpi Accumulate rec_def lp:{{
  get_rec {{ rec }}.
  get_def {{ def }}.
}}.

(* Definition msg_pubkey_right (rec: Type) (def: XDefault rec) := msg_pubkey.

Check  msg_sender.

Definition msg_sender_right (rec: Type) (def: XDefault rec) := msg_sender.
Check  msg_sender_right.


Definition msg_value_right (rec: Type) (def: XDefault rec) := msg_value.
Definition tvm_pubkey_right (rec: Type) (def: XDefault rec) := tvm_pubkey.
Definition _now_right (rec: Type) (def: XDefault rec) := \\ now \\.
 *)

Check constructor.

Definition constructor_exec_sig (_initialAmount :  uint256) 
                                (_tokenName :  string) 
                                (_decimalUnits :  uint8) 
                                (_tokenSymbol :  string) (l : LedgerLRecord rec) :
                                {t | t = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l}.
  unfold constructor. unfold dynamicAssignL.
  unfold totalSupply_left, balances_left, name_left, symbol_left, decimals_left.
  repeat auto_build_P listInfinite.
Defined.

Definition constructor_exec_let (_initialAmount :  uint256) 
                                (_tokenName :  string) 
                                (_decimalUnits :  uint8) 
                                (_tokenSymbol :  string) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2 @constructor_exec_sig (constructor_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Defined.

(* Print constructor_exec_let. *)

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


Print constructor_exec.


Definition transfer_exec_sig (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = exec_state (Uinterpreter (@transfer rec def _ _ _ _  _to _value)) l}.
  unfold transfer. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.