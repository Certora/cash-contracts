import "helpers/helpers.spec";
import "methods/IERC20.spec";
import "methods/MockIERC20.spec";
import "methods/IERC2612.spec";

methods {
    function isWhitelistedMinter(address) external returns (bool) envfree;
    function isWhitelistedRecipient(address) external returns (bool) envfree;

    // Getters:
    function factory() external returns (address) envfree;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Invariant: balance of address(0) is 0                                                                               │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
invariant zeroAddressNoBalance()
    balanceOf(0) == 0;

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: only mint and withdraw can change total supply                                                                   │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule noChangeTotalSupply(env e) {
    method f;
    calldataarg args;

    uint256 totalSupplyBefore = totalSupply();
    // avoid over/underflows when withdrawing and minting:
    if (f.selector == sig:mint(address,uint256).selector) {
        address to;
        uint256 amount; 
        require totalSupplyBefore + amount < max_uint256;
        mint(e, to, amount);
    } else if (f.selector == sig:withdraw(address,uint256).selector) {
        address to;
        uint256 amount; 
        require totalSupplyBefore > amount;
        withdraw(e, to, amount);
    } else {
        f(e, args);
    }
    uint256 totalSupplyAfter = totalSupply();

    assert totalSupplyAfter > totalSupplyBefore => f.selector == sig:mint(address,uint256).selector;
    assert totalSupplyAfter < totalSupplyBefore => f.selector == sig:withdraw(address,uint256).selector;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: only white listed minters can increase the total supply                                                      │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule onlyWhitelistedCanMint(env e) {
    method f;
    calldataarg args;
    address account;

    uint256 totalSupplyBefore   = totalSupply();
    // to avoid underflow while burning and have a false increase in total supply
    if (f.selector == sig:withdraw(address,uint256).selector) {
        address to;
        uint256 amount; 
        require totalSupplyBefore > amount;
        withdraw(e, to, amount);
    } else {
        f(e, args);
    }
    uint256 totalSupplyAfter    = totalSupply();

    assert (totalSupplyBefore < totalSupplyAfter) => isWhitelistedMinter(e.msg.sender);
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: only white listed recipients can have their balance increased                                               │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule onlyWhitelistedRecipientCanIncreaseTheirBalance(env e) {
    method f;
    calldataarg args;
    address account;

    require account != currentContract; // to avoid false violation by minting.

    uint256 balanceBefore   = balanceOf(account);
    f(e, args);
    uint256 balanceAfter    = balanceOf(account);

    assert (balanceBefore < balanceAfter) => isWhitelistedRecipient(account);
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: only the token holder (or a permit) can increase allowance. The spender can decrease it by using it          │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule onlyHolderOfSpenderCanChangeAllowance(env e) {
    // requireInvariant totalSupplyIsSumOfBalances();

    method f;
    calldataarg args;
    address holder;
    address spender;

    uint256 allowanceBefore = allowance(holder, spender);
    f(e, args);
    uint256 allowanceAfter = allowance(holder, spender);

    assert (
        allowanceAfter > allowanceBefore
    ) => (
        (f.selector == sig:approve(address,uint256).selector           && e.msg.sender == holder) ||
        (f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector)
    );

    assert (
        allowanceAfter < allowanceBefore
    ) => (
        (f.selector == sig:transferFrom(address,address,uint256).selector && e.msg.sender == spender) ||
        (f.selector == sig:approve(address,uint256).selector              && e.msg.sender == holder ) ||
        (f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector)
    );
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: mint behavior and side effects                                                                               │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule mint(env e) {
    require nonpayable(e);
    require e.msg.sender != 0; // fair assumption.
    require e.msg.sender != currentContract;

    address to;
    address other;
    uint256 amount;

    // cache state
    uint256 toBalanceBefore    = balanceOf(to);
    uint256 otherBalanceBefore = balanceOf(other);
    uint256 totalSupplyBefore  = totalSupply();

    // avoid overflow in wrapper
    require totalSupplyBefore + amount < max_uint256; // avoid overflow
    require toBalanceBefore + amount < max_uint256; // avoid overflow
    
    // cache state - base token
    uint256 baseTokenSenderBalanceBefore = mockERC20.balanceOf(e.msg.sender);
    uint256 baseTokenContractBalanceBefore = mockERC20.balanceOf(currentContract);
    uint256 contractAllowanceBefore = mockERC20.allowance(e.msg.sender, currentContract);

    // avoid overflow in baseToken
    require baseTokenContractBalanceBefore + amount < max_uint256; // avoid overflow

    // run transaction
    mint@withrevert(e, to, amount);

    // check outcome
    if (lastReverted) {
        assert to == 0 || 
        !isWhitelistedMinter(e.msg.sender) ||
        !isWhitelistedRecipient(to) ||
        baseTokenSenderBalanceBefore < amount ||
        contractAllowanceBefore < amount;
    } else {
        // updates balance and totalSupply - wrapper
        assert to_mathint(balanceOf(to)) == toBalanceBefore   + amount;
        assert to_mathint(totalSupply()) == totalSupplyBefore + amount;

        // no other balance is modified - wrapper
        assert balanceOf(other) != otherBalanceBefore => other == to;

        // updates balances and allowance - baseToken
        assert to_mathint(mockERC20.balanceOf(currentContract)) == baseTokenContractBalanceBefore + amount;
        assert to_mathint(mockERC20.allowance(e.msg.sender, currentContract)) == contractAllowanceBefore - amount || contractAllowanceBefore == max_uint256;

        // check whitelists
        assert isWhitelistedMinter(e.msg.sender);
        assert isWhitelistedRecipient(to);
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: withdraw behavior and side effects                                                                               │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule withdraw(env e) {
    require nonpayable(e);
    require e.msg.sender != 0; // fair assumption.
    require e.msg.sender != currentContract;

    address to;
    address other;
    uint256 amount;

    // cache state - wrapper
    uint256 senderBalanceBefore = balanceOf(e.msg.sender);
    uint256 otherBalanceBefore = balanceOf(other);
    uint256 totalSupplyBefore  = totalSupply();

    // avoid overflow in wrapper
    require totalSupplyBefore >= amount; // avoid underflow

    // cache state - base token
    uint256 baseTokenToBalanceBefore = mockERC20.balanceOf(to);
    uint256 baseTokenContractBalanceBefore = mockERC20.balanceOf(currentContract);
    uint256 baseTokenTotalSupplyBefore  = mockERC20.totalSupply();

    // avoid overflow in baseToken
    require baseTokenToBalanceBefore + amount < max_uint256; // avoid overflow

    // run transaction
    withdraw@withrevert(e, to, amount);

    // check outcome
    if (lastReverted) {
        assert e.msg.sender == 0 || 
        senderBalanceBefore < amount ||
        to == 0 ||
        baseTokenContractBalanceBefore < amount;
    } else {
        // updates balance and totalSupply - wrapper
        assert to_mathint(balanceOf(e.msg.sender)) == senderBalanceBefore - amount;
        assert to_mathint(totalSupply())   == totalSupplyBefore - amount;

        // no other balance is modified
        assert balanceOf(other) != otherBalanceBefore => other == e.msg.sender;

        // updates balances - base token
        assert mockERC20.balanceOf(to) == baseTokenToBalanceBefore + amount || to == currentContract;
        assert mockERC20.balanceOf(currentContract) == baseTokenContractBalanceBefore - amount || to == currentContract;
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rule: transfer behavior and side effects                                                                            │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule transfer(env e) {
    // requireInvariant totalSupplyIsSumOfBalances();
    require nonpayable(e);

    address holder = e.msg.sender;
    address recipient;
    address other;
    uint256 amount;

    // cache state
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);
    uint256 otherBalanceBefore     = balanceOf(other);

    // avoid overflow
    require holderBalanceBefore + recipientBalanceBefore < max_uint256;

    // run transaction
    transfer@withrevert(e, recipient, amount);

    // check outcome
    if (lastReverted) {
        assert holder == 0 || 
        recipient == 0 || 
        amount > holderBalanceBefore ||
        !isWhitelistedRecipient(recipient);
    } else {
        // balances of holder and recipient are updated
        assert to_mathint(balanceOf(holder))    == holderBalanceBefore    - (holder == recipient ? 0 : amount);
        assert to_mathint(balanceOf(recipient)) == recipientBalanceBefore + (holder == recipient ? 0 : amount);

        // no other balance is modified
        assert balanceOf(other) != otherBalanceBefore => (other == holder || other == recipient);
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rule: transferFrom behavior and side effects                                                                        │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule transferFrom(env e) {
    // requireInvariant totalSupplyIsSumOfBalances();
    require nonpayable(e);

    address spender = e.msg.sender;
    address holder;
    address recipient;
    address other;
    uint256 amount;

    // cache state
    uint256 allowanceBefore        = allowance(holder, spender);
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);
    uint256 otherBalanceBefore     = balanceOf(other);

    // avoid overflow
    require holderBalanceBefore + recipientBalanceBefore < max_uint256;

    // run transaction
    transferFrom@withrevert(e, holder, recipient, amount);

    // check outcome
    if (lastReverted) {
        assert holder == 0 || 
        recipient == 0 || 
        spender == 0 || 
        amount > holderBalanceBefore || 
        amount > allowanceBefore || 
        !isWhitelistedRecipient(recipient);
    } else {
        // allowance is valid & updated
        assert allowanceBefore            >= amount;
        assert to_mathint(allowance(holder, spender)) == (allowanceBefore == max_uint256 ? max_uint256 : allowanceBefore - amount);

        // balances of holder and recipient are updated
        assert to_mathint(balanceOf(holder))    == holderBalanceBefore    - (holder == recipient ? 0 : amount);
        assert to_mathint(balanceOf(recipient)) == recipientBalanceBefore + (holder == recipient ? 0 : amount);

        // no other balance is modified
        assert balanceOf(other) != otherBalanceBefore => (other == holder || other == recipient);
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rule: approve behavior and side effects                                                                             │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule approve(env e) {
    require nonpayable(e);

    address holder = e.msg.sender;
    address spender;
    address otherHolder;
    address otherSpender;
    uint256 amount;

    // cache state
    uint256 otherAllowanceBefore = allowance(otherHolder, otherSpender);

    // run transaction
    approve@withrevert(e, spender, amount);

    // check outcome
    if (lastReverted) {
        assert holder == 0 || spender == 0;
    } else {
        // allowance is updated
        assert allowance(holder, spender) == amount;

        // other allowances are untouched
        assert allowance(otherHolder, otherSpender) != otherAllowanceBefore => (otherHolder == holder && otherSpender == spender);
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rule: permit behavior and side effects                                                                              │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule permit(env e) {
    require nonpayable(e);

    address holder;
    address spender;
    uint256 amount;
    uint256 deadline;
    uint8 v;
    bytes32 r;
    bytes32 s;

    address account1;
    address account2;
    address account3;

    // cache state
    uint256 nonceBefore          = nonces(holder);
    uint256 otherNonceBefore     = nonces(account1);
    uint256 otherAllowanceBefore = allowance(account2, account3);

    // sanity: nonce overflow, which possible in theory, is assumed to be impossible in practice
    require nonceBefore      < max_uint256;
    require otherNonceBefore < max_uint256;

    // run transaction
    permit@withrevert(e, holder, spender, amount, deadline, v, r, s);

    // check outcome
    if (lastReverted) {
        // Without formally checking the signature, we can't verify exactly the revert causes
        assert true;
    } else {
        // allowance and nonce are updated
        assert allowance(holder, spender) == amount;
        assert to_mathint(nonces(holder)) == nonceBefore + 1;

        // deadline was respected
        assert deadline >= e.block.timestamp;

        // no other allowance or nonce is modified
        assert nonces(account1)              != otherNonceBefore     => account1 == holder;
        assert allowance(account2, account3) != otherAllowanceBefore => (account2 == holder && account3 == spender);
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rule: whitelistMinters behavior and side effects                                                                             │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule whitelistMinters(env e) {
    require nonpayable(e);

    address[] accounts;
    bool[] whitelists;
    // limit array size for simplicity
    require accounts.length <= 2;
    require whitelists.length <= 2;

    address account;
    require account != accounts[0] && account != accounts[1];

    bool isWhitelistedBefore = isWhitelistedMinter(account);

    // run transaction
    whitelistMinters@withrevert(e, accounts, whitelists);

    // check outcome
    if (lastReverted) {
        assert accounts.length != whitelists.length ||
        e.msg.sender != factory();
    } else {
        // minters whitelist is updated
        assert isWhitelistedBefore == isWhitelistedMinter(account);
        assert (accounts.length == 2 && accounts[0] != accounts[1]) || (accounts.length == 1) => isWhitelistedMinter(accounts[0]) == whitelists[0];
        assert accounts.length == 2 && accounts[0] == accounts[1] => isWhitelistedMinter(accounts[0]) == whitelists[1]; // the latest one is the actual update.
        assert accounts.length == 2 => isWhitelistedMinter(accounts[1]) == whitelists[1];
    }
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rule: whitelistRecipients behavior and side effects                                                                             │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule whitelistRecipients(env e) {
    require nonpayable(e);

    address[] accounts;
    bool[] whitelists;
    // limit array size for simplicity
    require accounts.length <= 2;
    require whitelists.length <= 2;

    address account;
    require account != accounts[0] && account != accounts[1];

    bool isWhitelistedBefore = isWhitelistedRecipient(account);

    // run transaction
    whitelistRecipients@withrevert(e, accounts, whitelists);

    // check outcome
    if (lastReverted) {
        assert accounts.length != whitelists.length ||
        e.msg.sender != factory();
    } else {
        // recipients whitelist is updated
        assert isWhitelistedBefore == isWhitelistedRecipient(account);
        assert (accounts.length == 2 && accounts[0] != accounts[1]) || (accounts.length == 1) => isWhitelistedRecipient(accounts[0]) == whitelists[0];
        assert accounts.length == 2 && accounts[0] == accounts[1] => isWhitelistedRecipient(accounts[0]) == whitelists[1]; // the latest one is the actual update.
        assert accounts.length == 2 => isWhitelistedRecipient(accounts[1]) == whitelists[1];
    }
}
