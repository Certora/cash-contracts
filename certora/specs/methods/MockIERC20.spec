using MockERC20 as mockERC20;

methods {
    function mockERC20.name()                                external returns (string)  envfree;
    function mockERC20.symbol()                              external returns (string)  envfree;
    function mockERC20.decimals()                            external returns (uint8)   envfree;
    function mockERC20.totalSupply()                         external returns (uint256) envfree;
    function mockERC20.balanceOf(address)                    external returns (uint256) envfree;
    function mockERC20.allowance(address,address)            external returns (uint256) envfree;
    function mockERC20.approve(address,uint256)              external returns (bool);
    function mockERC20.transfer(address,uint256)             external returns (bool);
    function mockERC20.transferFrom(address,address,uint256) external returns (bool);
}