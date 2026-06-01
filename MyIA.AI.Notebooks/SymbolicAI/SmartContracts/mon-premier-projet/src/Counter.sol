// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

contract Counter {
    // Une variable count (uint256)
    uint256 private count;

    // Une fonction increment() qui augmente count
    function increment() public {
        count += 1;
    }

    // Une fonction decrement() qui diminue count (si > 0)
    function decrement() public {
        require(count > 0, "Counter: count is already zero");
        count -= 1;
    }

    // Une fonction getCount() qui retourne count
    function getCount() public view returns (uint256) {
        return count;
    }
}
