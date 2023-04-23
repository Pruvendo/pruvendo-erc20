(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/trees*)

Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import IERC20.
Module ERC20.
#[translation = on]
#[language = solidity]
#[Contract = ERC20Contract]
Contract ERC20 ;
Sends To IERC20; 
Types ;
Constants ;
Record Contract := {
    totalSupply: uint256;
    balanceOf: mapping  ( address )( uint256 );
    allowance: mapping  ( address )( mapping  ( address )( uint256 ) );
    (* name: string;
    symbol: string;
    decimals: uint8 *)
}.
SetUrsusOptions.
UseLocal Definition _ := [
     boolean;
     address;
     uint256;

    (* added *)
     (mapping address uint256)
].
#[override, external, nonpayable,  returns=_result]
Ursus Definition transfer (recipient :  address) (amount :  uint256): UExpression ( boolean) false .
{
    :://  balanceOf[msg->sender] := balanceOf[msg->sender] - amount .
    :://  balanceOf[recipient]   := balanceOf[recipient] + amount .
    :://  send (* Transfer(msg->sender, recipient, amount) *) 
                IERC20.Transfer(msg->sender, recipient, amount) 
                => msg->sender 
                with {InternalMessageParamsLRecord} [$ {2} ⇒ {Message_ι_flag} $] .
    :://  _result := @true |.
}
return.
Defined.
Sync.

#[override, external, nonpayable,  returns=_result]
Ursus Definition approve (spender :  address) (amount :  uint256): UExpression ( boolean) false .
{
    :://  var θ :  mapping  ( address )( uint256 ) := allowance[msg->sender];_|. ::// θ[spender] := amount; allowance[msg->sender] := θ ;_|.
    :://  send (* Approval(msg->sender, spender, amount) *) 
                IERC20.Approval(msg->sender, spender, amount)
                => msg->sender 
                with {InternalMessageParamsLRecord} [$ {2} ⇒ {Message_ι_flag} $] .
    :://  _result := @true |.
}
return.
Defined.
Sync.

#[override, external, nonpayable,  returns=_result]
Ursus Definition transferFrom (sender :  address) (recipient :  address) (amount :  uint256): UExpression ( boolean) false .
{
    :://  var θ :  mapping  ( address )( uint256 ) := allowance[sender];_|. ::// θ[msg->sender] := θ[msg->sender] - amount; allowance[msg->sender] := θ ;_|.
    :://  balanceOf[sender] := balanceOf[sender] - amount .
    :://  balanceOf[recipient] := balanceOf[recipient] + amount .
    :://  send (* Transfer(sender, recipient, amount) *) 
                IERC20.Transfer(sender, recipient, amount) 
                => msg->sender 
                with {InternalMessageParamsLRecord} [$ {2} ⇒ {Message_ι_flag} $] .
    :://  _result := @true |.
}
return.
Defined.
Sync.

#[override, external, nonpayable]
Ursus Definition mint (amount :  uint256): UExpression PhantomType false .
{
    :://  balanceOf[msg->sender] := balanceOf[msg->sender] + amount .
    :://  totalSupply += amount .
    :://  send (* Transfer(address({0}), msg->sender, amount) *) 
                IERC20.Transfer((*address(#{0})*) {}, msg->sender, amount) 
                => msg->sender 
                with {InternalMessageParamsLRecord} [$ {2} ⇒ {Message_ι_flag} $] |.
}
return.
Defined.
Sync.

#[override, external, nonpayable]
Ursus Definition burn (amount :  uint256): UExpression PhantomType false .
{
    :://  balanceOf[msg->sender] := balanceOf[msg->sender] - amount .
    :://  totalSupply-=amount .
    :://  send (* Transfer(msg->sender, address({0}), amount) *) 
                IERC20.Transfer(msg->sender, (*address({0})*) {}, amount) 
                => msg->sender 
                with {InternalMessageParamsLRecord} [$ {2} ⇒ {Message_ι_flag} $] |.
}
return.
Defined.
Sync.
EndContract Implements.
End ERC20.