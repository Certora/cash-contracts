// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Test, console, stdError} from "forge-std/Test.sol";
import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {UserSafeFactory} from "../../src/user-safe/UserSafeFactory.sol";
import {UserSafe, OwnerLib} from "../../src/user-safe/UserSafe.sol";
import {UserSafeV2Mock} from "../../src/mocks/UserSafeV2Mock.sol";
import {Swapper1InchV6} from "../../src/utils/Swapper1InchV6.sol";
import {PriceProvider} from "../../src/oracle/PriceProvider.sol";
import {CashDataProvider} from "../../src/utils/CashDataProvider.sol";

import {Upgrades} from "openzeppelin-foundry-upgrades/Upgrades.sol";

contract UserSafeFactoryTest is Test {
    using OwnerLib for address;
    address owner = makeAddr("owner");

    address etherFiRecoverySigner = makeAddr("etherFiRecoverySigner");
    address thirdPartyRecoverySigner = makeAddr("thirdPartyRecoverySigner");
    address etherFiRecoverySafe = makeAddr("etherFiRecoverySafe");

    UserSafeFactory factory;
    UserSafe impl;
    UserSafeV2Mock implV2;

    ERC20 usdc = ERC20(0xaf88d065e77c8cC2239327C5EDb3A432268e5831);
    ERC20 weETH = ERC20(0x35751007a407ca6FEFfE80b3cB397736D2cf4dbe);
    Swapper1InchV6 swapper;
    PriceProvider priceProvider;
    CashDataProvider cashDataProvider;

    uint256 defaultSpendingLimit = 10000e6;
    uint64 withdrawalDelay = 10;
    address etherFiCashMultisig = makeAddr("multisig");
    address etherFiCashDebtManager = makeAddr("debtManager");

    address weEthWethOracle = 0xE141425bc1594b8039De6390db1cDaf4397EA22b;
    address ethUsdcOracle = 0x639Fe6ab55C921f74e7fac1ee960C0B6293ba612;
    address swapRouter1InchV6 = 0x111111125421cA6dc452d289314280a0f8842A65;

    address alice = makeAddr("alice");
    bytes aliceBytes = abi.encode(alice);
    address bob = makeAddr("bob");
    bytes bobBytes = abi.encode(bob);

    UserSafe aliceSafe;
    UserSafe bobSafe;

    function setUp() public {
        vm.createSelectFork("https://rpc.ankr.com/arbitrum");
        address[] memory assets = new address[](1);
        assets[0] = address(weETH);

        vm.startPrank(owner);
        swapper = new Swapper1InchV6(swapRouter1InchV6, assets);
        priceProvider = new PriceProvider(weEthWethOracle, ethUsdcOracle);

        address proxy = Upgrades.deployUUPSProxy(
            "CashDataProvider.sol:CashDataProvider",
            abi.encodeWithSelector(
                // intiailize(address,uint64,address,address,address,address,address,address,address)
                0x04dfc293,
                owner,
                withdrawalDelay,
                etherFiCashMultisig,
                etherFiCashDebtManager,
                address(usdc),
                address(weETH),
                address(priceProvider),
                address(swapper),
                etherFiRecoverySafe
            )
        );
        cashDataProvider = CashDataProvider(proxy);

        impl = new UserSafe(
            address(cashDataProvider),
            etherFiRecoverySigner,
            thirdPartyRecoverySigner
        );

        implV2 = new UserSafeV2Mock(
            address(cashDataProvider),
            etherFiRecoverySigner,
            thirdPartyRecoverySigner
        );

        factory = new UserSafeFactory(address(impl), owner);

        aliceSafe = UserSafe(
            factory.createUserSafe(
                abi.encodeWithSelector(
                    // initialize(bytes,uint256)
                    0x458c5191,
                    aliceBytes,
                    defaultSpendingLimit
                )
            )
        );

        bobSafe = UserSafe(
            factory.createUserSafe(
                abi.encodeWithSelector(
                    // initialize(bytes,uint256)
                    0x458c5191,
                    bobBytes,
                    defaultSpendingLimit
                )
            )
        );

        vm.stopPrank();
    }

    function test_Deploy() public view {
        assertEq(aliceSafe.owner().ethAddr, alice);
        assertEq(bobSafe.owner().ethAddr, bob);
    }

    function test_Upgrade() public {
        vm.prank(owner);
        factory.upgradeTo(address(implV2));

        UserSafeV2Mock aliceSafeV2 = UserSafeV2Mock(address(aliceSafe));
        UserSafeV2Mock bobSafeV2 = UserSafeV2Mock(address(bobSafe));

        assertEq(aliceSafeV2.version(), 2);
        assertEq(bobSafeV2.version(), 2);
        assertEq(aliceSafeV2.usdc(), cashDataProvider.usdc());
        assertEq(aliceSafeV2.weETH(), cashDataProvider.weETH());
    }
}
