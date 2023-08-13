Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import EIP20Interface.

Module EIP20.

#[translation = off]
#[language = solidity]
Contract EIP20 ;
Sends To (* *) ; 
Inherits (* *) ; 
Types (*  *);
Constants 
Definition MAX_UINT256 : uint256 := (N.pow 10 256) - 1;

Record Contract := {
    #[public] balances: mapping address uint256;
    #[public] allowed: mapping address (mapping address uint256);
    #[public] name: string;
    #[public] decimals: uint8;
    #[public] symbol: string;
    #[public] totalSupply: uint256
}.

SetUrsusOptions.
Unset Ursus Extraction.

UseLocal Definition _ := [
     uint256;
     string;
     uint8;
     boolean;
     address;
     mapping address uint256
].

#[override (* ??? *), public, nonpayable]
Ursus Definition constructor (_initialAmount :  uint256) 
                             (_tokenName :  string) 
                             (_decimalUnits :  uint8) 
                             (_tokenSymbol :  string) : UExpression PhantomType false.
{
    :://  balances[[msg->sender]] := _initialAmount .
    :://  totalSupply := _initialAmount .
    :://  name := _tokenName .
    :://  decimals := _decimalUnits .
    :://  symbol := _tokenSymbol |.
}
return.
Defined.
Sync.

#[public]
Ursus Definition var_test1 (arg1: uint256) (arg2: uint256)
                           (arg3: uint256) (arg4: uint256)
                           (arg5: uint256) (arg6: uint256): UExpression PhantomType false.
{
    :://  arg1 := {0} .
    :://  arg2 := {0} .    
    :://  arg3 := {0} |.    
}
return.
Defined.
Sync.


#[public]
Ursus Definition var_test2 : UExpression PhantomType false.
{
    ::// var arg1 : uint256; _ |.  
    ::// var arg2 : uint256; _ |.
    ::// var arg3 : uint256; _ |.
    ::// var arg4 : uint256; _ |.
    ::// var arg5 : uint256; _ |.
    ::// var arg6 : uint256; _ |.

    (* ::// require_ (arg1 > arg2). *)

    :://  arg1 := {0} .
    :://  arg2 := {0} .    
    :://  arg3 := {0} |.
}
return.
Defined.
Sync.

#[public]
Ursus Definition var_test3 (arg1: uint256) (arg2: uint256)
                           (arg3: uint256) (arg4: uint256)
                           (arg5: uint256) (arg6: uint256) : UExpression PhantomType false.
{
    ::// var arg11 : uint256; _ |.  
    ::// var arg22 : uint256; _ |.
    ::// var arg33 : uint256; _ |.
    ::// var arg44 : uint256; _ |.
    ::// var arg55 : uint256; _ |.
    ::// var arg66 : uint256; _ |.
    ::// {var_test2}  |.
}
return.
Defined.
Sync.

#[public]
Ursus Definition var_test4 (arg1: uint256) (arg2: uint256)
                           (arg3: uint256) (arg4: uint256)
                           (arg5: uint256) (arg6: uint256) : UExpression PhantomType false.
{
    ::// var arg11 : uint256; _ |.  
    ::// var arg22 : uint256; _ |.
    ::// var arg33 : uint256; _ |.
    ::// var arg44 : uint256; _ |.
    ::// var arg55 : uint256; _ |.
    ::// var arg66 : uint256; _ |.
    ::// arg1 := {0} |.
}
return.
Defined.
Sync.


#[override, public, nonpayable, returns = success]
Ursus Definition transfer (_to :  address) 
                          (_value :  uint256): UExpression boolean true .
{
    :://  require_ ( balances [[msg->sender]] >= _value ) .    
    :://  balances [[ msg->sender ]] -=  _value .
    :://  balances [[ _to ]] += _value .
    (* :://  Transfer(msg->sender, _to, _value). *)
    :://  success := @true |.
}
return.
Defined.
Sync.


(* #[override, public, nonpayable,  returns = success] *)
Definition transferFrom_ls_payload (_from : ULValue address) 
                               (_to : ULValue address) 
                               (_value : ULValue uint256)
                               (_success: ULValue boolean)
                               (_allowance : ULValue uint256) : UExpression boolean true.
    
    ::// {_allowance} := allowed[[_from]][[msg->sender]] ; _ |.
    :://  require_(((balances[[_from]] >= _value) && ({_allowance} >= _value))) .
    :://  balances[[_to]] += _value .
    :://  balances[[_from]] -= _value .
    :://  if ( {_allowance} < MAX_UINT256 ) then 
          {
            allowed[[_from]][[msg->sender]] -= _value
          } .    
    :://  _success := @true |.
Defined.
(*  *)

#[override, public, nonpayable,  returns = success]
Ursus Definition transferFrom_ls_template (_from :  address) 
                                      (_to :  address) 
                                      (_value :  uint256): UExpression boolean true.
{
    :://  var allowance : uint256 ; _ |.
    ::// {transferFrom_ls_payload _from _to _value  success allowance } |.
}
return.
Defined.
Sync.


#[override, public, nonpayable,  returns = success]
Ursus Definition transferFrom (_from :  address) 
                              (_to :  address) 
                              (_value :  uint256): UExpression boolean true.
{
    :://  var allowance : uint256  := allowed[[_from]][[msg->sender]] ; _ |.
    :://  require_(((balances[[_from]] >= _value) && ({allowance} >= _value))) .
    :://  balances[[_to]] += _value .
    :://  balances[[_from]] -= _value .
    :://  if ( {allowance} < MAX_UINT256 ) then 
          {
            allowed[[_from]][[msg->sender]] -= _value
          } .
    (* :://  Transfer(_from, _to, _value). *)
    :://  success := @true |.
}
return.
Defined.
Sync.


#[override, public, nonpayable, returns = success]
Ursus Definition transfer' (_to :  address) 
                           (_value :  uint256)
                           (b: bool): UExpression boolean true .
{
    :://  require_ ( b ) .    
    :://  balances [[ msg->sender ]] -=  _value .
    :://  balances [[ _to ]] += _value .    
    :://  success := @true |.
}
return.
Defined.
Sync.

#[override, public, nonpayable, returns = success]
Ursus Definition transfer1 (_to :  address) 
                          (_value :  uint256): UExpression boolean true .
{
    ::// success := transfer' (_to, _value, balances [[msg->sender]] >= _value) |.
}
return.
Defined.
Sync.

#[override, public, nonpayable, returns = success]
Ursus Definition transferFrom1 (_from :  address) 
                              (_to :  address) 
                              (_value :  uint256): UExpression boolean true.
{
    ::// var allowance : uint256  := allowed[[_from]][[msg->sender]] ; _ |.
    ::// success := transfer' (_to, _value, ((balances[[_from]] >= _value) && 
                                            ({allowance} >= _value))) .
    ::// if ( {allowance} < MAX_UINT256 ) then 
          {
            allowed[[_from]][[msg->sender]] -= _value
          } |.
}
return.
Defined.
Sync.


#[override, public, view,  returns = balance]
Ursus Definition balanceOf (_owner :  address): UExpression uint256 false .
{
    :://  {balance} := balances[[_owner]] |.
}
return.
Defined.
Sync.

#[override, public, nonpayable,  returns = success]
Ursus Definition approve (_spender :  address) (_value :  uint256): UExpression boolean false .
{
    ::// allowed[[msg->sender]][[_spender]] := _value .
    (* :://  Approval(msg->sender, _spender, _value). *)
    :://  success := @true |.
}
return.
Defined.
Sync.

#[override, public, view,  returns=remaining]
Ursus Definition allowance (_owner :  address) (_spender :  address) : UExpression uint256 false .
{
    :://  remaining := allowed[[_owner]][[_spender]] |.
}
return.
Defined.
Sync.

EndContract Implements EIP20Interface.
End EIP20.

GenerateLocalState 0 EIP20.
GenerateLocalState EIP20.
