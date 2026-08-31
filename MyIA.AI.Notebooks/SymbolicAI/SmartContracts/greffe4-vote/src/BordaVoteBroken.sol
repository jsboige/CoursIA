// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @title BordaVoteBroken
/// @notice Version volontairement cassée de BordaVote pour le contrôle négatif.
///         Le bug : `pts` n'est pas borné — un bulletin classant un candidat
///         **multiple fois** (le même rang répété) lui attribue plusieurs fois
///         les points, et un rang `i` avec `i >= maxRank` est accepté (pas de
///         garde `require`). L'invariant I2 (`scores[candidate] <= maxRank` si
///         un candidat n'apparaît qu'une fois par bulletin) est violé.
///
/// C'est le témoin que le fuzzing de #13570 est **discriminant** : un fuzzer
/// qui ne découvre rien ici est un fuzzer qui n'a rien cherché.
contract BordaVoteBroken {
    uint256 public constant maxRank = 3;

    mapping(address => bool) public hasVoted;
    uint256 public totalBallots;
    uint256 public totalRankedCandidates;

    mapping(address => mapping(uint256 => uint256)) public voterPoints;
    mapping(uint256 => uint256) public scores;

    event BallotCast(address indexed voter, uint256[] ranked, uint256 points);

    function castBallot(uint256[] calldata ranked) external {
        require(!hasVoted[msg.sender], "voter already voted");
        require(ranked.length > 0, "empty ballot");
        // BUG : pas de garde `ranked.length <= maxRank`. Un bulletin peut
        // classer plus de `maxRank` candidats, ou le même candidat plusieurs
        // fois. `pts` peut donc dépasser `maxRank` pour un candidat.

        hasVoted[msg.sender] = true;
        totalBallots += 1;
        totalRankedCandidates += ranked.length;

        for (uint256 i = 0; i < ranked.length; i++) {
            uint256 cand = ranked[i];
            uint256 pts = maxRank - i;
            // Si i > maxRank, `maxRank - i` underflow (0.8 revert), mais pour
            // i == 0..maxRank le même candidat peut revenir plusieurs fois :
            // scores[c] est incrémenté plusieurs fois pour UN bulletin.
            scores[cand] += pts;
            voterPoints[msg.sender][cand] = pts;
        }

        emit BallotCast(msg.sender, ranked, ranked.length);
    }

    function scoreOf(uint256 cand) external view returns (uint256) {
        return scores[cand];
    }

    function winner(uint256[] calldata candidates) external view returns (uint256) {
        uint256 best = 0;
        uint256 bestScore = 0;
        for (uint256 i = 0; i < candidates.length; i++) {
            uint256 s = scores[candidates[i]];
            if (s > bestScore) {
                bestScore = s;
                best = candidates[i];
            }
        }
        return best;
    }
}
