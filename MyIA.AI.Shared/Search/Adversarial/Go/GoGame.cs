namespace MyIA.AI.Shared.Search.Adversarial.Go;

/// <summary>
/// Couleur d'une intersection de goban, vide comprise.
/// </summary>
public enum GoColor
{
    /// <summary>Intersection vide.</summary>
    Empty = 0,

    /// <summary>Pierre noire — joue en premier.</summary>
    Black = 1,

    /// <summary>Pierre blanche.</summary>
    White = 2,
}

/// <summary>Extensions de <see cref="GoColor"/>.</summary>
public static class GoColorExtensions
{
    /// <summary>La couleur opposée — le vide est son propre opposé.</summary>
    public static GoColor Opposite(this GoColor color) => color switch
    {
        GoColor.Black => GoColor.White,
        GoColor.White => GoColor.Black,
        _ => GoColor.Empty,
    };
}

/// <summary>
/// Une intersection du goban, ou le coup de passe (<see cref="Pass"/>).
/// </summary>
/// <param name="X">Colonne, 0 inclusif, croissant vers la droite.</param>
/// <param name="Y">Ligne, 0 inclusif, croissant vers le bas.</param>
public readonly record struct GoPoint(int X, int Y)
{
    /// <summary>Le coup de passe — jouer nulle part.</summary>
    public static GoPoint Pass => new(-1, -1);

    /// <summary>Ce point est-il le coup de passe ?</summary>
    public bool IsPass => X < 0;

    /// <summary>
    /// Nom de coordonnee a la GTP : colonnes lettrees en sautant I
    /// (A B C D E F G H J K...), lignes numerotees depuis le bas. C'est la
    /// convention que le patrimoine lisait dans la sortie gnugo
    /// (<c>final_status_list</c>) ; elle est posee ici des le moteur de
    /// regles pour que la future tranche GTP n'ait pas de traduction a faire.
    /// </summary>
    public override string ToString()
    {
        if (IsPass)
        {
            return "pass";
        }

        const string letters = "ABCDEFGHJKLMNOPQRSTUVWXYZ";
        return $"{letters[X]}{Y + 1}";
    }
}

/// <summary>
/// Moteur de regles du jeu de Go : placement, captures, suicide, ko simple,
/// passes et score de territoire. Port des semantiques du <c>GoBoard</c> de
/// GoTraxx (patrimoine Aricie, <c>Libraries/AI/external/GoTraxx/</c>), EPIC
/// #7265 pepite B3, tranche 2.
/// </summary>
/// <remarks>
/// <para>
/// <b>Ce qui est porte, et d'ou.</b> L'ordre de legalite est celui de
/// <c>GoBoard.IsLegal</c> : passe toujours legale, puis sur-plateau, puis
/// intersection vide, puis non-violation du ko simple, puis non-suicide. Le
/// suicide est defini comme chez GoTraxx : un coup n'est PAS suicidaire s'il
/// touche une intersection vide, ou une chaine amie qui garde une liberte
/// ailleurs, ou une chaine ennemie dont il prend la DERNIERE liberte (le
/// capturer d'abord est la reponse canonique au suicide apparent). Le ko
/// simple est pose exactement comme GoTraxx le pose dans
/// <c>ExecutePlay</c> : quand un coup capture exactement UN groupe d'UNE
/// pierre et que la pierre jouee n'a AUCUN voisin ami (pierre isolee), la
/// position de la pierre capturee devient interdite au coup suivant. Toute
/// pierre jouee ensuite efface le point de ko. La partie se termine par deux
/// passes consecutifs. Les prisonniers sont comptes par couleur, comme le
/// <c>CapturedStoneCnt</c> du patrimoine.
/// </para>
/// <para>
/// <b>Delta assume avec la source.</b> GoTraxx maintenait des structures
/// incrementales (GoBlock fusionnes a chaque coup, pile d'undo, hachage
/// Zobrist pour le superko, regions de surete) : ce port recalcule groupes et
/// libertes par flood-fill local, ce qui est equivalent pour les regles et
/// suppose plus lent pour un moteur de recherche — l'adaptateur IGame
/// (tranche 3, apres le merge de #19176) mesurera ce cout. Le superko
/// <b>est porte</b> (tranche 4) : positionnel, par empreinte Zobrist 64 bits
/// deterministe, l'historique des positions survivant au clonage — sans lui,
/// l'arbre de recherche de la tranche 3 pourrait boucler sur un cycle que la
/// racine interdit. Le resign, le chargement SGF et l'evaluation CNTK ne sont
/// pas portes. Deux ecritures propres au patrimoine ne sont pas conservees : il
/// envisageait de jouer hors tour (<c>IsSimpleKoViolation</c> testait
/// <c>Turn != player</c>) — ici l'alternance est stricte ; le score vivait
/// chez un gnugo externe — ici c'est un score de territoire (pieres + vides
/// encercles d'une seule couleur, komi compris), le seul calculable sans
/// oracle exterieur.
/// </para>
/// </remarks>
public sealed class GoGame
{
    private readonly GoColor[] _board;
    private readonly int[] _captured;           // prisonniers, indexes par valeur de l'enum
    private int _koIndex = -1;                  // GoTraxx SimpleKoPoint (-1 = aucun)
    private int _consecutivePasses;
    private ulong _positionHash;                // XOR Zobrist des pierres posees
    private HashSet<ulong> _positionHistory;    // chaque position vue depuis l'ouverture (superko)

    /// <summary>
    /// Tables Zobrist par taille de plateau, deux entrees par intersection (noir,
    /// puis blanc). Valeurs issues d'un SplitMix64 a graine fixe : deterministes
    /// d'une execution a l'autre, contrairement a un tirage aleatoire — un temoin
    /// de legalite ne doit pas dependre du tirage qui l'a precede.
    /// </summary>
    private static readonly Dictionary<int, ulong[]> ZobristCache = new();

    /// <summary>Plateau carre, taille 2 a 25.</summary>
    public int Size { get; }

    /// <summary>Komi — compensation du blanc, ajoutee a son score de territoire.</summary>
    public double Komi { get; }

    /// <summary>Couleur au trait — noir en ouverture.</summary>
    public GoColor ToPlay { get; private set; } = GoColor.Black;

    /// <summary>La partie est-elle terminee (deux passes consecutifs) ?</summary>
    public bool IsOver { get; private set; }

    /// <summary>
    /// Le point de ko simple courant, s'il existe — la position de la pierre
    /// capturable qu'un recapture immediat reprendrait. Informationnelle :
    /// <see cref="IsLegal(GoPoint)"/> l'applique deja.
    /// </summary>
    public GoPoint? KoPoint => _koIndex < 0 ? null : PointOf(_koIndex);

    /// <summary>
    /// Empreinte Zobrist 64 bits de la position courante (pierres posees, pas le
    /// trait). Informationnelle — sert de temoin aux tests ; la legalite superko
    /// la recalcule elle-meme. Une collision 64 bits entre deux positions reelles
    /// est possible en principe (anniversaire : ~2^32 positions) et negligeable en
    /// pratique : une partie plafonne a quelques centaines de positions.
    /// </summary>
    public ulong PositionHash => _positionHash;

    /// <summary>Nombre de positions distinctes vues depuis l'ouverture, vide compris.</summary>
    public int PositionCount => _positionHistory.Count;

    /// <summary>Plateau vide, noir au trait.</summary>
    public GoGame(int size = 19, double komi = 7.5)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(size, 2);
        ArgumentOutOfRangeException.ThrowIfGreaterThan(size, 25);
        Size = size;
        Komi = komi;
        _board = new GoColor[size * size];
        _captured = new int[3];
        _positionHistory = new HashSet<ulong> { 0UL };
    }

    /// <summary>
    /// Copie profonde et independante du plateau. Le contrat fonctionnel
    /// <c>IGame.Result</c> de la tranche 3 exige qu'un resultat ne mute pas son
    /// origine : chaque noeud de l'arbre de recherche est un clone, aucune
    /// mutation partagee. Toute l'information de partie y survit -- trait, ko,
    /// passes consecutifs, prisonniers, et l'historique de positions du superko :
    /// un clone qui l'oublierait autoriserait en sous-arbre la repetition que la
    /// racine interdit.
    /// </summary>
    public GoGame Clone()
    {
        GoGame copy = new(Size, Komi);
        Array.Copy(_board, copy._board, _board.Length);
        Array.Copy(_captured, copy._captured, _captured.Length);
        copy._koIndex = _koIndex;
        copy._consecutivePasses = _consecutivePasses;
        copy.ToPlay = ToPlay;
        copy.IsOver = IsOver;
        copy._positionHash = _positionHash;
        copy._positionHistory = new HashSet<ulong>(_positionHistory);
        return copy;
    }

    /// <summary>
    /// Copie profonde et independante du plateau. Le contrat fonctionnel
    /// <c>IGame.Result</c> de la tranche 3 exige qu'un resultat ne mute pas son
    /// origine : chaque noeud de l'arbre de recherche est un clone, aucune
    /// mutation partagee. Toute l'information de partie y survit -- trait, ko,
    /// passes consecutifs, prisonniers.
    /// </summary>
    public GoGame Clone()
    {
        GoGame copy = new(Size, Komi);
        Array.Copy(_board, copy._board, _board.Length);
        Array.Copy(_captured, copy._captured, _captured.Length);
        copy._koIndex = _koIndex;
        copy._consecutivePasses = _consecutivePasses;
        copy.ToPlay = ToPlay;
        copy.IsOver = IsOver;
        return copy;
    }

    /// <summary>Couleur posee a ce point.</summary>
    public GoColor ColorAt(GoPoint p) => _board[IndexOf(p)];

    /// <summary>
    /// Pierres de cette couleur capturees (retirees du plateau) depuis
    /// l'ouverture — le <c>CapturedStoneCnt</c> du patrimoine.
    /// </summary>
    public int CapturedStones(GoColor prisonerColor) =>
        prisonerColor == GoColor.Empty ? 0 : _captured[(int)prisonerColor];

    /// <summary>Legalite du coup pour la couleur au trait.</summary>
    public bool IsLegal(GoPoint p) => IsLegal(p, ToPlay);

    /// <summary>
    /// Legalite dans l'ordre du patrimoine : sur-plateau, intersection vide,
    /// pas de violation du ko simple, pas de suicide, puis pas de repetition
    /// de position (superko positionnel). L'alternance est stricte : seul le
    /// trait courant obtient vrai. Le passe est toujours legal — c'est la
    /// soupape d'arbitrage qui termine les parties sans coup, et la repetition
    /// qu'il produit est deja l'etat courant, pas une recreation.
    /// </summary>
    public bool IsLegal(GoPoint p, GoColor color)
    {
        if (color != ToPlay || IsOver)
        {
            return false;
        }

        if (p.IsPass)
        {
            return true;
        }

        int idx = IndexOf(p);
        if (_board[idx] != GoColor.Empty)
        {
            return false;
        }

        if (idx == _koIndex)
        {
            return false;
        }

        if (IsSuicide(idx, color))
        {
            return false;
        }

        return !RecreatesPosition(idx, color);
    }

    /// <summary>
    /// Le coup recreerait-il une position deja vue ? Superko positionnel : la
    /// position comparee est le plateau de pierres, trait exclu (le choix
    /// Tromp-Taylor ; le superko situationnel ajouterait le trait, plus dur
    /// encore). Le recapture immediat du ko simple est deja couvert par
    /// <c>_koIndex</c> ; ce qui reste vise sont les cycles longs — triple ko,
    /// double ko, envoi-de-deux-retour-d'un — qu'aucune regle locale n'attrape.
    /// </summary>
    private bool RecreatesPosition(int idx, GoColor color)
    {
        ulong candidate = _positionHash ^ ZobristStone(idx, color);
        foreach (int s in StonesCapturedBy(idx, color))
        {
            candidate ^= ZobristStone(s, color.Opposite());
        }

        return _positionHistory.Contains(candidate);
    }

    /// <summary>Jouer le coup pour la couleur au trait. Faux (rien ne bouge) si illegal.</summary>
    public bool Play(GoPoint p) => Play(p, ToPlay);

    /// <summary>
    /// Jouer une pierre (ou passer, <see cref="GoPoint.Pass"/>). Faux — et le
    /// plateau reste intact — si le coup est illegal.
    /// </summary>
    public bool Play(GoPoint p, GoColor color)
    {
        if (!IsLegal(p, color))
        {
            return false;
        }

        // Toute pierre jouee, passe comprise, efface le point de ko — le ko
        // simple n'interdit que le recapture IMMEDIAT (GoTraxx reinitialisait
        // SimpleKoPoint a chaque coup).
        _koIndex = -1;

        if (p.IsPass)
        {
            _consecutivePasses++;
            if (_consecutivePasses >= 2)
            {
                IsOver = true;
            }
        }
        else
        {
            _consecutivePasses = 0;
            int idx = IndexOf(p);
            bool loneStone = !HasNeighbor(idx, color);
            List<int> captured = StonesCapturedBy(idx, color);

            // Empreinte de la position produite, pierres capturees comprises.
            ulong candidate = _positionHash ^ ZobristStone(idx, color);
            foreach (int s in captured)
            {
                candidate ^= ZobristStone(s, color.Opposite());
                _board[s] = GoColor.Empty;
            }

            _board[idx] = color;
            _captured[(int)color.Opposite()] += captured.Count;

            // Ko simple, exactement comme GoTraxx le pose : une seule pierre
            // capturee, par une pierre isolee — le point interdit est la
            // position de la pierre capturee.
            _koIndex = captured.Count == 1 && loneStone
                ? captured[0]
                : -1;

            // La position produite est nouvelle par construction (le superko
            // l'a verifie en legalite) : l'inscrire est un fait, pas un pari.
            _positionHash = candidate;
            _positionHistory.Add(candidate);
        }

        ToPlay = color.Opposite();
        return true;
    }

    /// <summary>Passer son tour pour la couleur au trait.</summary>
    public bool Pass() => Play(GoPoint.Pass);

    /// <summary>
    /// Score de territoire (a la chinoise) : pour chaque couleur, pierres
    /// posees plus intersections vides entourees d'elle seule ; le komi
    /// s'ajoute au blanc. Positif = noir gagne.
    /// </summary>
    public double AreaScore()
    {
        bool[] visited = new bool[Size * Size];
        int blackArea = 0;
        int whiteArea = 0;

        for (int i = 0; i < _board.Length; i++)
        {
            if (_board[i] == GoColor.Black)
            {
                blackArea++;
            }
            else if (_board[i] == GoColor.White)
            {
                whiteArea++;
            }
            else if (!visited[i])
            {
                // Region vide inedite : elle appartient a la seule couleur qui
                // la borde, si elle est unique — sinon a personne (dame).
                int regionSize = 0;
                bool touchesBlack = false;
                bool touchesWhite = false;
                Queue<int> queue = new();
                queue.Enqueue(i);
                visited[i] = true;
                while (queue.Count > 0)
                {
                    int c = queue.Dequeue();
                    regionSize++;
                    foreach (int n in Neighbors(c))
                    {
                        if (_board[n] == GoColor.Empty && !visited[n])
                        {
                            visited[n] = true;
                            queue.Enqueue(n);
                        }
                        else if (_board[n] == GoColor.Black)
                        {
                            touchesBlack = true;
                        }
                        else if (_board[n] == GoColor.White)
                        {
                            touchesWhite = true;
                        }
                    }
                }

                if (touchesBlack && !touchesWhite)
                {
                    blackArea += regionSize;
                }
                else if (touchesWhite && !touchesBlack)
                {
                    whiteArea += regionSize;
                }
            }
        }

        return blackArea - whiteArea - Komi;
    }

    /// <summary>
    /// Suicide au sens du patrimoine : toutes les voisines sont occupees,
    /// aucune chaine amie ne garde de liberte ailleurs, et aucune chaine
    /// ennemie n'est capturee par ce coup.
    /// </summary>
    private bool IsSuicide(int idx, GoColor color)
    {
        foreach (int n in Neighbors(idx))
        {
            if (_board[n] == GoColor.Empty)
            {
                return false;
            }

            (_, HashSet<int> liberties) = Group(n);
            if (_board[n] == color)
            {
                // Une chaine amie qui respirerait encore sans cette intersection.
                if (liberties.Count > 1)
                {
                    return false;
                }
            }
            else
            {
                // Une chaine ennemie dont ce coup prend la derniere liberte.
                if (liberties.Count == 1 && liberties.Contains(idx))
                {
                    return false;
                }
            }
        }

        return true;
    }

    private bool HasNeighbor(int idx, GoColor color)
    {
        foreach (int n in Neighbors(idx))
        {
            if (_board[n] == color)
            {
                return true;
            }
        }

        return false;
    }

    /// <summary>
    /// Pierres ennemies que ce coup capturerait, sans toucher au plateau. Une
    /// chaine peut toucher l'intersection jouee par plusieurs de ses pierres :
    /// le dedoublonnage par appartenance evite de la compter deux fois — le
    /// <c>Play</c> d'origine s'en tirait en vidant le plateau au fil du scan,
    /// mutation qu'une sonde de legalite ne peut pas se permettre.
    /// </summary>
    private List<int> StonesCapturedBy(int idx, GoColor color)
    {
        List<int> captured = new();
        foreach (int n in Neighbors(idx))
        {
            if (_board[n] != color.Opposite() || captured.Contains(n))
            {
                continue;
            }

            (List<int> stones, HashSet<int> liberties) = Group(n);
            if (liberties.Count == 1 && liberties.Contains(idx))
            {
                captured.AddRange(stones);
            }
        }

        return captured;
    }

    /// <summary>Entree Zobrist d'une pierre de cette couleur a cette intersection.</summary>
    private ulong ZobristStone(int idx, GoColor color) =>
        ZobristTable(Size)[((int)color - 1) * Size * Size + idx];

    /// <summary>
    /// Table Zobrist de cette taille de plateau, construite une fois par taille
    /// et partagee par toutes les parties de meme taille. SplitMix64 a graine
    /// fixe : deux executions produisent la meme table.
    /// </summary>
    private static ulong[] ZobristTable(int size)
    {
        lock (ZobristCache)
        {
            if (!ZobristCache.TryGetValue(size, out ulong[]? table))
            {
                table = new ulong[2 * size * size];
                ulong state = 0x2545F4914F6CDD1DUL ^ (uint)size;
                for (int i = 0; i < table.Length; i++)
                {
                    state += 0x9E3779B97F4A7C15UL;
                    ulong z = state;
                    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
                    z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
                    table[i] = z ^ (z >> 31);
                }

                ZobristCache[size] = table;
            }

            return table!;
        }
    }

    /// <summary>Chaine et libertes de la pierre a cette intersection (flood-fill).</summary>
    private (List<int> Stones, HashSet<int> Liberties) Group(int idx)
    {
        GoColor color = _board[idx];
        List<int> stones = new();
        HashSet<int> liberties = new();
        bool[] seen = new bool[Size * Size];
        Queue<int> queue = new();
        queue.Enqueue(idx);
        seen[idx] = true;
        while (queue.Count > 0)
        {
            int c = queue.Dequeue();
            stones.Add(c);
            foreach (int n in Neighbors(c))
            {
                if (_board[n] == GoColor.Empty)
                {
                    liberties.Add(n);
                }
                else if (_board[n] == color && !seen[n])
                {
                    seen[n] = true;
                    queue.Enqueue(n);
                }
            }
        }

        return (stones, liberties);
    }

    private IEnumerable<int> Neighbors(int idx)
    {
        int x = idx % Size;
        int y = idx / Size;
        if (x > 0)
        {
            yield return idx - 1;
        }

        if (x < Size - 1)
        {
            yield return idx + 1;
        }

        if (y > 0)
        {
            yield return idx - Size;
        }

        if (y < Size - 1)
        {
            yield return idx + Size;
        }
    }

    private int IndexOf(GoPoint p)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(p.X);
        ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(p.X, Size);
        ArgumentOutOfRangeException.ThrowIfNegative(p.Y);
        ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(p.Y, Size);
        return p.Y * Size + p.X;
    }

    private GoPoint PointOf(int idx) => new(idx % Size, idx / Size);
}
