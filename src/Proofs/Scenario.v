Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import Common.
Require Import Proofs.Constructor.
Require Import Proofs.Transfer.
Require Import Proofs.TransferFrom.


Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.




(* mint to some address
    1. create token
    2. mint (transfer) _value to _to*)
Lemma MintToSomeAddress_set_recepient_balance: forall 
                            (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string) 

                            (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec)
                            (l0: LedgerLRecord rec)
                            (l1: LedgerLRecord rec)
                            (l2: LedgerLRecord rec), 
(*     let l0 := {$$ default with Ledger_VMState := vmstate $$} in
    let l1 := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let l2 := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l1 in
 *) l = default ->
 l0 = {$$ l with Ledger_LocalState := default $$} ->
    l1 = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 ->
    let l1' := {$$ l1 with Ledger_LocalState := default $$} in
    l2 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l1' ->
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    (xIntGeb _initialAmount  _value = true) ->
    _to <> msg_sender ->
    (_balances (l2.(Ledger_MainState))) [_to] = _value.
Proof.
    intros.
    subst l2.
    subst l1'.
    rewrite transfer_set_recepient_balance.
    match goal with
    | |- context [if ?b then _ else _] => assert (b = true)
    end.
    rewrite <- H3.
     assert (VMState_ι_msg_sender (Ledger_VMState l1) = msg_sender).
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged. auto.
    rewrite H2.
     subst l1.
    subst l0.
    subst msg_sender.
    rewrite constructor_set_sender_balance. auto.
    rewrite H2.
    subst l1.
    subst l0.
    rewrite constructor_not_sender_balance.

    all: cycle 1.
    auto.
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged. auto.
    subst l.

    compute; buint_all; auto.
    erewrite lookup_none_find.
    all: cycle 1. 
    compute; buint_all; auto.
    destruct _value.
    simpl.
    f_equal.
Qed.


(* transfer to third address
    1. create token
    2. mint (transfer) _value1 to address1
    2'. change sender (change VMState)
    3. transfer _value2 to address2*)
Lemma TransferToThirdAddress_set_recepient_balance: forall 
    (_initialAmount :  uint256) 
    (_tokenName :  string) 
    (_decimalUnits :  uint8) 
    (_tokenSymbol :  string) 

    (address1 :  address) 
    (address2 :  address) 
    (value1 : uint256)
    (value2 : uint256)
    (vmstate1: VMStateLRecord)
    (l: LedgerLRecord rec)
    (l0: LedgerLRecord rec)
    (l1: LedgerLRecord rec)
    (l2: LedgerLRecord rec) 
    (l3: LedgerLRecord rec), 
 
    l0 = {$$ l with Ledger_LocalState := default $$} ->
    l1 = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 ->
let l1' := {$$ l1 with Ledger_LocalState := default $$} in
    l2 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ address1 value1)) l1' ->
let l2' := {$$ l2 with Ledger_LocalState := default $$} in
let l2'' := {$$ l2' with Ledger_VMState := vmstate1 $$} in
    l3 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ address2 value2)) l2'' ->
let msg_sender := VMState_ι_msg_sender (l0.(Ledger_VMState)) in
let msg_sender1 := VMState_ι_msg_sender (l2''.(Ledger_VMState)) in
(xIntGeb _initialAmount  value1 = true) ->
(xIntGeb value1  value2 = true) ->
(* address1 <> msg_sender ->
 *)address2 <> msg_sender ->
address1 <> address2 ->
address1 = msg_sender1 ->
(_balances (l3.(Ledger_MainState))) [address2] = value2.
Proof.
Abort.

(* transfer to third address
    1. create token
    2. mint (transfer) _value1 to address1
    2'. change sender (change VMState)
    3. Set allowance (approve) by address1 to address2 (value2)
    3'. change sender (change VMState)
    4. transfer _value3 from address1 to address3 by address2*)
Lemma TransferToThirdAddress_set_recepient_balance: forall 
    (_initialAmount :  uint256) 
    (_tokenName :  string) 
    (_decimalUnits :  uint8) 
    (_tokenSymbol :  string) 

    (address1 :  address) 
    (address2 :  address) 
    (address3 :  address) 
    (value1 : uint256)
    (value2 : uint256)
    (value3 : uint256)
    (vmstate1: VMStateLRecord) 
    (vmstate2: VMStateLRecord)
    (l: LedgerLRecord rec)
    (l0: LedgerLRecord rec)
    (l1: LedgerLRecord rec)
    (l2: LedgerLRecord rec) 
    (l3: LedgerLRecord rec) 
    (l4: LedgerLRecord rec), 
 
    l0 = {$$ l with Ledger_LocalState := default $$} ->
    l1 = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 ->
let l1' := {$$ l1 with Ledger_LocalState := default $$} in
    l2 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ address1 value1)) l1' ->
let l2' := {$$ l2 with Ledger_LocalState := default $$} in
let l2'' := {$$ l2' with Ledger_VMState := vmstate1 $$} in
    l3 = exec_state (Uinterpreter (@approve rec def _ _ _  address2 value2)) l2'' ->
let l3' := {$$ l3 with Ledger_LocalState := default $$} in
let l3'' := {$$ l3' with Ledger_VMState := vmstate2 $$} in
    l4 = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ address1 address3 value3)) l3'' ->
let msg_sender := VMState_ι_msg_sender (l0.(Ledger_VMState)) in
let msg_sender1 := VMState_ι_msg_sender (l2''.(Ledger_VMState)) in
let msg_sender2 := VMState_ι_msg_sender (l3''.(Ledger_VMState)) in
(xIntGeb _initialAmount  value1 = true) ->
(xIntGeb value1  value3 = true) ->
(xIntGeb value2  value3 = true) ->
address3 <> msg_sender ->
address3 <> address1 ->
address1 = msg_sender1 ->
address2 = msg_sender2 ->
(_balances (l4.(Ledger_MainState))) [address3] = value3.
Proof.
Abort.

