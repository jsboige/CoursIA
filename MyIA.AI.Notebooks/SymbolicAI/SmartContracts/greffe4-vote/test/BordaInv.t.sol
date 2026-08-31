// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;
import "forge-std/Test.sol";
import "../src/BordaVote.sol";
import "../src/BordaVoteBroken.sol";

/// @title BordaInvariants
/// @notice Invariants SC-13 du comptage Borda (Greffe 4, #13570) — contrat CORRECT.
///
/// L'invariant central est **I2** : un bulletin Borda valide (candidats
/// distincts, au plus `maxRank` d'entre eux) attribue à un candidat au plus
/// `maxRank` points ; donc globalement `scores[c] <= maxRank * totalBallots`.
///
/// Le contrat `BordaVote` rejette les bulletins qui re-classent un candidat
/// (`require` d'unicité) et ceux qui dépassent `maxRank`. Le harnais `cast`
/// simule des électeurs DISTINCTS (le fuzzer peut donc empiler de nombreux
/// bulletins) en mappant ses entrées vers 4 candidats et des longueurs 1-3 :
/// sous fuzzing, I2 se maintient — le fuzzer ne peut pas faire céder la borne.
///
/// Le témoin que ce fuzzing n'est pas décoratif vit dans `BrokenFuzz.t.sol` :
/// les MÊMES invariants, ciblés sur le contrat cassé, ÉCHOuent (le fuzzer y
/// découvre un contre-exemple).
contract BordaInvariants is Test {
    BordaVote vote;
    uint256 voterCounter;

    function setUp() public {
        vote = new BordaVote();
        // Le fuzzer cible ce harnais : `cast` est la seule fonction externe
        // mutante, les `invariant_*` sont les propriétés à maintenir.
        targetContract(address(this));
    }

    /// @notice Harnais : chaque appel du fuzzer simule un **électeur distinct**
    ///         (le contrat réel limite à un vote par adresse — les bulletins
    ///         multiples doivent venir d'adresses différentes). Les entrées
    ///         fuzzées sont mappées vers 4 candidats {0,1,2,3} et une longueur
    ///         1-3 : l'espace des bulletins est petit et dense, le fuzzer
    ///         exerce toutes les formes (y compris invalides, rejetées).
    function cast(uint8 a, uint8 b, uint8 c, uint8 n) external {
        uint256 len = n % 3 + 1;
        uint256[] memory ranked = new uint256[](len);
        ranked[0] = a % 4;
        if (len > 1) ranked[1] = b % 4;
        if (len > 2) ranked[2] = c % 4;
        address v = address(uint160((voterCounter % 999) + 1));
        voterCounter += 1;
        vm.prank(v);
        try vote.castBallot(ranked) {} catch {}
    }

    /// @notice I2 (borne Borda) : sous fuzzing, aucun candidat ne dépasse
    ///         `maxRank * totalBallots`.
    function invariant_scoreNeverExceedsBound() public view {
        for (uint256 c = 0; c < 4; c++) {
            assertLe(vote.scoreOf(c), vote.maxRank() * vote.totalBallots());
        }
    }

    /// @notice I1 (conservation) : la somme des points Borda sur tous les
    ///         candidats reste bornée par `maxRank * totalRankedCandidates`
    ///         (chaque emplacement classé rapporte au plus `maxRank` points).
    function invariant_pointsConserved() public view {
        uint256 total = 0;
        for (uint256 c = 0; c < 4; c++) {
            total += vote.scoreOf(c);
        }
        assertLe(total, vote.maxRank() * vote.totalRankedCandidates());
    }

    /// @notice Contrôle positif : le contrat CORRECT rejette un bulletin qui
    ///         re-classe un candidat — c'est la garde qui rend I2 tenable.
    function test_correctRejectsDuplicateCandidate() public {
        uint256[] memory ranked = new uint256[](2);
        ranked[0] = 7;
        ranked[1] = 7;
        vm.expectRevert("duplicate candidate");
        vote.castBallot(ranked);
    }

    /// @notice Comptage exact sur un bulletin valide : rang 0 → maxRank points,
    ///         rang 1 → maxRank - 1, etc.
    function test_bordaPointsByRank() public {
        uint256[] memory ranked = new uint256[](2);
        ranked[0] = 7;
        ranked[1] = 8;
        vote.castBallot(ranked);
        assertEq(vote.scoreOf(7), vote.maxRank());
        assertEq(vote.scoreOf(8), vote.maxRank() - 1);
    }

    /// @notice **Témoin déterministe** : le contrat CASSÉ accepte le
    ///         re-classement et viole I2 (`3 + 2 = 5 > maxRank = 3`).
    ///         Le fuzzer qui découvre la même violation de son côté vit dans
    ///         `BrokenFuzz.t.sol`.
    function test_brokenViolatesBound() public {
        BordaVoteBroken broken = new BordaVoteBroken();
        uint256[] memory ranked = new uint256[](2);
        ranked[0] = 7;
        ranked[1] = 7;
        broken.castBallot(ranked);
        assertGt(broken.scoreOf(7), broken.maxRank(), "I2 viole : re-classer un candidat depasse la borne Borda");
    }
}
