// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import "forge-std/Test.sol";
import "../src/BordaVoteBroken.sol";

/// @title BrokenInvariants
/// @notice Les MÊMES invariants que `BordaInvariants`, ciblés sur le contrat
///         VOLONTAIREMENT CASSÉ (`BordaVoteBroken`) — Greffe 4, #13570.
///
/// Ce contrat de test est conçu pour **ÉCHOUER** : c'est le contrôle négatif
/// exigé par le critère 3 de #13570 (« au moins un invariant qui échoue sur
/// une version volontairement cassée — un fuzzing toujours vert ne prouve pas
/// la robustesse, il prouve que le fuzzer n'a rien cherché »).
///
/// Le contrat cassé n'a ni garde d'unicité ni borne de longueur : un bulletin
/// `[c, c]` attribue à `c` les points `maxRank + (maxRank - 1) = 5 > 3` en un
/// seul bulletin. Le fuzzer, qui mappe ses entrées vers 4 candidats et des
/// longueurs 1-3, produit un tel bulletin en quelques appels et casse I2.
///
/// Ne PAS l'inclure dans la suite verte : il se lance ciblé, depuis le
/// notebook, avec `forge test --match-contract BrokenInvariants` — sa sortie
/// rouge (contre-exemple + séquence d'appels) EST le livrable.
contract BrokenInvariants is Test {
    BordaVoteBroken broken;
    uint256 voterCounter;

    function setUp() public {
        broken = new BordaVoteBroken();
        targetContract(address(this));
    }

    /// @notice Même harnais que `BordaInvariants.cast` — électeurs distincts,
    ///         4 candidats, longueurs 1-3. Sur le contrat cassé, les bulletins
    ///         dupliqués ne sont PAS rejetés : ils passent et sur-attribuent.
    function cast(uint8 a, uint8 b, uint8 c, uint8 n) external {
        uint256 len = n % 3 + 1;
        uint256[] memory ranked = new uint256[](len);
        ranked[0] = a % 4;
        if (len > 1) ranked[1] = b % 4;
        if (len > 2) ranked[2] = c % 4;
        address v = address(uint160((voterCounter % 999) + 1));
        voterCounter += 1;
        vm.prank(v);
        try broken.castBallot(ranked) {} catch {}
    }

    /// @notice I2 — DOIT échouer ici : le fuzzer dépose un bulletin dupliqué,
    ///         un candidat dépasse `maxRank` en un seul bulletin.
    function invariant_scoreNeverExceedsBound() public view {
        for (uint256 c = 0; c < 4; c++) {
            assertLe(broken.scoreOf(c), broken.maxRank() * broken.totalBallots());
        }
    }
}
