// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {DebtManagerSetup} from "./DebtManagerSetup.t.sol";
import {IL2DebtManager} from "../../src/interfaces/IL2DebtManager.sol";
import {SafeERC20, IERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {IERC20Errors} from "@openzeppelin/contracts/interfaces/draft-IERC6093.sol";

contract DebtManagerLiquidateTest is DebtManagerSetup {
    using SafeERC20 for IERC20;

    uint256 collateralAmount = 0.01 ether;
    uint256 collateralValueInUsdc;
    uint256 borrowAmt;

    function setUp() public override {
        super.setUp();

        collateralValueInUsdc = debtManager.convertCollateralTokenToUsdc(
            address(weETH),
            collateralAmount
        );

        deal(address(usdc), alice, 1 ether);
        deal(address(usdc), owner, 1 ether);
        deal(address(weETH), alice, 1000 ether);
        // so that debt manager has funds for borrowings
        deal(address(usdc), address(debtManager), 1 ether);

        vm.startPrank(alice);
        IERC20(address(weETH)).safeIncreaseAllowance(address(debtManager), collateralAmount);
        debtManager.depositCollateral(address(weETH), alice, collateralAmount);

        borrowAmt = debtManager.remainingBorrowingCapacityInUSDC(alice);

        debtManager.borrow(address(usdc), borrowAmt);
        vm.stopPrank();
    }

    function test_SetLiquidationThreshold() public {
        uint256 newThreshold = 70e18;
        vm.prank(owner);
        debtManager.setLtvAndLiquidationThreshold(
            address(weETH),
            ltv,
            newThreshold
        );
        (, uint256 _liquidationThreshold) = debtManager.collateralTokenConfig(
            address(weETH)
        );

        assertEq(_liquidationThreshold, newThreshold);
    }

    function test_OnlyAdminCanSetLiquidationThreshold() public {
        uint256 newThreshold = 70e18;
        vm.startPrank(notOwner);
        vm.expectRevert(
            buildAccessControlRevertData(notOwner, debtManager.ADMIN_ROLE())
        );
        debtManager.setLtvAndLiquidationThreshold(
            address(weETH),
            ltv,
            newThreshold
        );

        vm.stopPrank();
    }

    function test_Liquidate() public {
        vm.startPrank(owner);

        uint256 liquidatorWeEthBalBefore = weETH.balanceOf(owner);

        debtManager.setLtvAndLiquidationThreshold(address(weETH), 5e18, 10e18);
        assertEq(debtManager.liquidatable(alice), true);

        IERC20(address(usdc)).forceApprove(address(debtManager), borrowAmt);
        debtManager.liquidate(alice, address(usdc), borrowAmt);

        vm.stopPrank();

        uint256 aliceCollateralAfter = debtManager.getCollateralValueInUsdc(
            alice
        );
        uint256 aliceDebtAfter = debtManager.borrowingOf(alice, address(usdc));
        uint256 liquidatorWeEthBalAfter = weETH.balanceOf(owner);

        assertApproxEqAbs(
            debtManager.convertCollateralTokenToUsdc(
                address(weETH),
                liquidatorWeEthBalAfter - liquidatorWeEthBalBefore
            ),
            borrowAmt,
            10
        );
        assertEq(aliceCollateralAfter, collateralValueInUsdc - borrowAmt);
        assertEq(aliceDebtAfter, 0);
    }

    function test_PartialLiquidate() public {
        vm.startPrank(owner);

        debtManager.setLtvAndLiquidationThreshold(address(weETH), 5e18, 10e18);
        assertEq(debtManager.liquidatable(alice), true);

        // since we will be setting the liquidation threshold to 10%
        uint256 maxBorrow = collateralValueInUsdc / 10;
        uint256 liquidatorWeEthBalBefore = weETH.balanceOf(owner);
        uint256 liquidationAmt = borrowAmt - (maxBorrow / 3);

        IERC20(address(usdc)).forceApprove(address(debtManager), liquidationAmt);
        debtManager.liquidate(alice, address(usdc), liquidationAmt);

        vm.stopPrank();

        uint256 aliceCollateralAfter = debtManager.getCollateralValueInUsdc(
            alice
        );
        uint256 aliceDebtAfter = debtManager.borrowingOf(alice, address(usdc));
        uint256 liquidatorWeEthBalAfter = weETH.balanceOf(owner);

        assertApproxEqAbs(
            debtManager.convertCollateralTokenToUsdc(
                address(weETH),
                liquidatorWeEthBalAfter - liquidatorWeEthBalBefore
            ),
            liquidationAmt,
            10
        );
        assertApproxEqAbs(
            aliceCollateralAfter,
            collateralValueInUsdc - liquidationAmt,
            10
        );
        assertApproxEqAbs(aliceDebtAfter, maxBorrow / 3, 10);
    }

    function test_CannotLiquidateIfNotLiquidatable() public {
        vm.startPrank(owner);
        assertEq(debtManager.liquidatable(alice), false);
        IERC20(address(usdc)).forceApprove(address(debtManager), borrowAmt);
        vm.expectRevert(IL2DebtManager.CannotLiquidateYet.selector);
        debtManager.liquidate(alice, address(usdc), borrowAmt);

        vm.stopPrank();
    }
}
