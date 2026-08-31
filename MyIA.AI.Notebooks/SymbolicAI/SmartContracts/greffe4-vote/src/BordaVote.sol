// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @title BordaVote
/// @notice Comptage Borda sur chaîne. S'attend à des bulletins de la forme
///         `(voter, candidateRanked[i])` où `candidateRanked` liste les
///         candidats **par ordre de préférence décroissante** (le premier est
///         le préféré). Un candidat absent d'un bulletin obtient 0 point.
///
/// Greffe 4 (#13570) — la règle d'agrégation est nommée (Borda) et vivante sur
/// chaîne (EVM), pas un compteur hors-ligne. Le résultat du comptage est l'audit
/// (on-chain), et les invariants sont fuzzés (SC-13).
///
/// --- Invariants exposés ------------------------------------------------
/// Les invariants ci-dessous sont ce que le fuzzer SC-13 doit maintenir :
///   I1  `totalRankedCandidates == somme des candidats classés sur tous les bulletins`
///   I2  `scores[c] <= maxRank` pour tout candidat c (bornes Borda)
///   I3  `scores[c]` d'un candidat présent dans un bulletin augmente de
///       `maxRank - rang` pour celui-ci (pas de double comptage / compte de
///       tous les bulletins)
///
/// Le contrat volontairement cassé (BordaVoteBroken) viole I2 (pas de borne),
/// ce qui rend le fuzzing **discriminant** : un invariant faux n'est pas une
/// décoration si un contrat cassé le fait échouer.
// ------------------------------------------------------------------------ //
contract BordaVote {
    uint256 public constant maxRank = 3;

    mapping(address => bool) public hasVoted;
    uint256 public totalBallots;
    uint256 public totalRankedCandidates;

    // `voter -> candidate -> points attribués par ce voter`
    mapping(address => mapping(uint256 => uint256)) public voterPoints;
    // `candidate -> total Borda`
    mapping(uint256 => uint256) public scores;

    event BallotCast(address indexed voter, uint256[] ranked, uint256 points);

    /// @notice Dépôt d'un bulletin Borda. `ranked[0]` est le préféré.
    /// @param ranked Candidats classés, préférence décroissante, distincts.
    function castBallot(uint256[] calldata ranked) external {
        require(!hasVoted[msg.sender], "voter already voted");
        require(ranked.length > 0, "empty ballot");
        require(ranked.length <= maxRank, "rank exceeds bound");
        // Borda compte chaque candidat au plus une fois par bulletin : un même
        // candidat classé deux fois permettrait de sur-attribuer ses points et
        // violerait I2 sous fuzzing.
        for (uint256 i = 0; i < ranked.length; i++) {
            for (uint256 j = i + 1; j < ranked.length; j++) {
                require(ranked[i] != ranked[j], "duplicate candidate");
            }
        }

        hasVoted[msg.sender] = true;
        totalBallots += 1;
        totalRankedCandidates += ranked.length;

        // Borda : un candidat au rang i (0-based) reçoit (maxRank - i) points.
        for (uint256 i = 0; i < ranked.length; i++) {
            uint256 cand = ranked[i];
            uint256 pts = maxRank - i;
            scores[cand] += pts;
            voterPoints[msg.sender][cand] = pts;
        }

        emit BallotCast(msg.sender, ranked, ranked.length);
    }

    /// @notice Score Borda total d'un candidat.
    function scoreOf(uint256 cand) external view returns (uint256) {
        return scores[cand];
    }

    /// @notice Gagnant : candidat au score maximal. Égalité possible.
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
