Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import EvalExecs.Constructor.

#[local]
Existing Instance BoolEq.pair_eqb_spec.


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


Lemma constructor_set__initialAmount: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (vmstate: VMStateLRecord), 
    let l0 := {$$ default with Ledger_VMState := vmstate $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _totalSupply (l'.(Ledger_MainState)) = _initialAmount.
Proof.
    intros. subst l'.
    rewrite <- constructor_prf.
    auto.
Qed.

Lemma constructor_set__tokenName: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (vmstate: VMStateLRecord), 
    let l0 := {$$ default with Ledger_VMState := vmstate $$} in                            
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _name (l'.(Ledger_MainState)) = _tokenName.
Proof.
    intros. subst l'.
    rewrite <- constructor_prf.
    auto.
Qed.

Lemma constructor_set__decimalUnits: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (vmstate: VMStateLRecord), 
    let l0 := {$$ default with Ledger_VMState := vmstate $$} in                                
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _decimals (l'.(Ledger_MainState)) = _decimalUnits.
Proof.
    intros. subst l'.
    rewrite <- constructor_prf.
    auto.
Qed.

Lemma constructor_set__tokenSymbol: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (vmstate: VMStateLRecord), 
    let l0 := {$$ default with Ledger_VMState := vmstate $$} in 
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _symbol (l'.(Ledger_MainState)) = _tokenSymbol.
Proof.
    intros. subst l'.
    rewrite <- constructor_prf.
    auto.
Qed.



Lemma constructor_set_sender_balance: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
                            (* (vmstate: VMStateLRecord),  *)
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    (_balances (l'.(Ledger_MainState))) [msg_sender] = _initialAmount.
Proof.
    intros. subst l'.
    rewrite <- constructor_prf.

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.

    Opaque Common.hmapFindWithDefault
           CommonInstances.addAdjustListPair.

    compute.

    Transparent Common.hmapFindWithDefault
                CommonInstances.addAdjustListPair.

    rewrite lookup_some_find with (v:=_initialAmount).
    reflexivity.
    
    unshelve eapply lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.
