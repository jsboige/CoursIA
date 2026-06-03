// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/Counter.sol";

contract CounterTest is Test {
    Counter counter;

    function setUp() public {
        counter = new Counter();
    }

    // Verifie que increment() fonctionne
    function testIncrement() public {
        assertEq(counter.getCount(), 0);
        counter.increment();
        assertEq(counter.getCount(), 1);
        counter.increment();
        assertEq(counter.getCount(), 2);
    }

    // Verifie que decrement() fonctionne
    function testDecrement() public {
        counter.increment();
        counter.increment();
        assertEq(counter.getCount(), 2);
        counter.decrement();
        assertEq(counter.getCount(), 1);
    }

    // Verifie qu'on ne peut pas decrementer sous zero
    function testDecrementZero() public {
        assertEq(counter.getCount(), 0);
        vm.expectRevert(bytes("Cannot decrement below zero"));
        counter.decrement();
    }

    // Verifie que le getter automatique public count() et getCount() sont coherents
    function testPublicGetter() public {
        counter.increment();
        assertEq(counter.count(), 1);
        assertEq(counter.count(), counter.getCount());
    }
}
