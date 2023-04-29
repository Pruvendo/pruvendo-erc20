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

Definition transfer_exec_let (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2 @transfer_exec_sig (transfer_exec_sig _to _value l).
Defined.

(* Print constructor_exec_let. *)

Definition transfer_exec (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @transfer_exec_let (transfer_exec_let _to _value l).
Defined.

Definition transfer_prf (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transfer_exec _to _value l = 
  exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l.
  proof_of_2 transfer_exec transfer_exec_sig (transfer_exec_sig _to _value l).
Defined.

(************************************************************************************************************************)

Print ContractFields.

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

Print VMStateFields.
#[local]
Existing Instance BoolEq.pair_eqb_spec.
Require Import FinProof.Lib.HMapList.

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

(************************************************************)

Lemma transfer_set_sender_balance: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let msg_sender_balance0 := (_balances (l.(Ledger_MainState))) [msg_sender] in
    msg_sender <> _to -> 
    (_balances (l'.(Ledger_MainState))) [msg_sender] = 
        if (xIntGeb msg_sender_balance0  _value : bool) then 
        xIntMinus msg_sender_balance0 _value
        else msg_sender_balance0.
Proof.        
    intros. subst l'.
    rewrite <- transfer_prf.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.

    Opaque Common.hmapFindWithDefault
           CommonInstances.addAdjustListPair
           N.add N.sub N.leb N.ltb N.eqb Z.eqb.    

    compute.    

    match goal with
    | |- context [@addAdjustListPair _ _ _ a ?v _] => remember v
    end.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros.

    match goal with
    | |- context [@Common.hmapFindWithDefault ?XBool ?XInteger
                                             ?XList ?XMaybe ?XProd 
                                             ?XHMap ?H0 ?H1 ?H4 ?H6
                                             ?K ?V ?v a _ _ ] => 
                                             remember (@Common.hmapFindWithDefault XBool XInteger
                                             XList XMaybe XProd 
                                             XHMap H0 H1 H4 H6
                                             K V v a) as find_a

    end.

    match goal with
    | |- context [@addAdjustListPair ?K ?V ?H a _ _ ] => 
                 remember (@addAdjustListPair K V H a) as adj_a
    end.

    match goal with
    | |- context [@addAdjustListPair ?K ?V ?H ?k _ _ ] => 
                 remember k as k1

    end.

    Transparent Common.hmapFindWithDefault
            CommonInstances.addAdjustListPair
            N.eqb
            Z.eqb.

    compute in Heqk1.
    subst k1.

    rewrite Heqfind_a.
    erewrite lookup_some_find.
    reflexivity.

    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    rewrite Heqadj_a.
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.

    assert (b = b0).
    rewrite Heqb, Heqb0, Heqfind_a.
    auto.

    rewrite Heqx16, Heqfind_a. 
    rewrite <- H1, H0.
    auto.

    assumption.

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.

    assert (b = b0).
    rewrite Heqb, Heqb0.
    auto.

    rewrite <- H1, H0.
    auto.
Qed.

