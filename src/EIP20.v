(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/trees*)

Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import EIP20Interface.
Module EIP20.
#[translation = on]
#[language = solidity]
#[Contract = EIP20Contract]
Contract EIP20 ;
Sends To (*need fix*) (**) ; 
(* Inherits   (**) ; *)
Types ;
Constants 
Definition MAX_UINT256 : uint256 := 100000000000 (*2**256 - 1 how to write power in coq?*);
Record Contract := {
    balances: mapping  ( address )( uint256 );
    allowed: mapping  ( address )( mapping  ( address )( uint256 ) );
    name: string;
    decimals: uint8;
    symbol: string;
    totalSupply: uint256
}.
SetUrsusOptions.
UseLocal Definition _ := [
     uint256;
     string;
     uint8;
     boolean;
     address;

     mapping address uint256
].
#[override, public, nonpayable]
Ursus Definition constructor (_initialAmount :  uint256) (_tokenName :  string) (_decimalUnits :  uint8) (_tokenSymbol :  string): UExpression PhantomType false .
{
    :://  balances[msg->sender]:=_initialAmount .
    :://  totalSupply:=_initialAmount .
    :://  name:=_tokenName .
    :://  decimals:=_decimalUnits .
    :://  symbol:=_tokenSymbol  |.
}
return.
Defined.
Sync.

#[override, public, nonpayable,  returns=success]
Ursus Definition transfer (_to :  address) (_value :  uint256): UExpression ( boolean) true .
{
    :://  require_((balances[msg->sender] >= _value)) .
    :://  balances[msg->sender] := balances[msg->sender] - _value .
    :://  balances[_to] := balances[_to] + _value .
    (* :://  Transfer(msg->sender, _to, _value). *)
    :://  success := @true |.
}
return.
Defined.
Sync.

#[override, public, nonpayable,  returns=success]
Ursus Definition transferFrom (_from :  address) (_to :  address) (_value :  uint256): UExpression ( boolean) true .
{
    :://  var allowance :  uint256  := allowed[_from][msg->sender] ;_|.
    :://  require_(((balances[_from] >= _value) && ({allowance} >= _value))) .
    :://  balances[_to] := balances[_to] + _value .
    :://  balances[_from] := balances[_from] - _value .
    :://  if ( ({allowance} < MAX_UINT256) ) then { {_:UExpression _ false} } .
    {
        (* :://  allowed[_from][msg->sender]-=_value  |. *)
        ::// var θ : ( mapping  ( address )( uint256 ) ) := allowed[_from]; _|. ::// θ[msg->sender] := θ[msg->sender] - _value. ::// allowed[_from] := θ |.
    }
    (* :://  Transfer(_from, _to, _value). *)
    :://  success := @true |.
}
return.
Defined.
Sync.

#[override, public, view,  returns=balance]
Ursus Definition balanceOf (_owner :  address): UExpression ( uint256) false .
{
    :://  {balance} := balances[_owner] |.
}
return.
Defined.
Sync.

#[override, public, nonpayable,  returns=success]
Ursus Definition approve (_spender :  address) (_value :  uint256): UExpression ( boolean) false .
{
    (* :://  allowed[msg->sender][_spender]:=_value . *)
    ::// var θ : ( mapping  ( address )( uint256 ) ) := allowed[msg->sender]; _|. ::// θ[_spender] := _value. ::// allowed[msg->sender] := θ .
    (* :://  Approval(msg->sender, _spender, _value). *)
    :://  success := @true |.
}
return.
Defined.
Sync.

#[override, public, view,  returns=remaining]
Ursus Definition allowance (_owner :  address) (_spender :  address): UExpression ( uint256) false .
{
    :://  remaining := allowed[_owner][_spender] |.
}
return.
Defined.
Sync.
EndContract Implements EIP20Interface.
End EIP20.

Goal True. idtac "EIP20 compiled". auto. Qed.