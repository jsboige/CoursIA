"""Generate SC-20-Bitcoin-Scripting.ipynb - Bitcoin, UTXO et Scripts."""
import json
import os


def md(source_text, cell_id):
    lines = source_text.split('\n')
    source = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            source.append(line + '\n')
        else:
            if line:
                source.append(line)
    return {"cell_type": "markdown", "id": cell_id, "metadata": {}, "source": source}


def code(source_text, cell_id):
    lines = source_text.split('\n')
    source = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            source.append(line + '\n')
        else:
            if line:
                source.append(line)
    return {"cell_type": "code", "id": cell_id, "metadata": {}, "source": source,
            "outputs": [], "execution_count": None}


cells = []

# === HEADER ===
cells.append(md(
"# SC-20-Bitcoin-Scripting - Bitcoin, UTXO et Scripts\n"
"\n"
"**Navigation** : [Index](../README.md) | [<< Ripple XRP](SC-19-Ripple-XRP.ipynb) | [Move Sui >>](SC-21-Move-Sui.ipynb)\n"
"\n"
"---\n"
"\n"
"## Objectifs d'apprentissage\n"
"\n"
"1. Comprendre le **modele UTXO** de Bitcoin et ses differences avec le modele Account d'Ethereum\n"
"2. Decouvrir **Bitcoin Script**, le langage a pile de Bitcoin\n"
"3. Implementer un **mini-interpreteur Bitcoin Script** en Python\n"
"4. Construire et signer des **transactions Bitcoin** manuellement\n"
"5. Explorer les **scripts avances** : multisig, timelock, P2SH\n"
"\n"
"### Prerequis\n"
"\n"
"- Python 3.10+ avec `hashlib` (stdlib)\n"
"- `python-bitcoinlib` (optionnel, pour la section 3)\n"
"\n"
"### Duree estimee : 50 minutes", "header"))

# === SECTION 1: MODELE UTXO ===
cells.append(md(
"---\n"
"\n"
"## 1. Le modele UTXO\n"
"\n"
"Bitcoin utilise un modele fondamentalement different d'Ethereum pour representer les soldes.\n"
"Au lieu d'un **modele Account** (chaque adresse a un solde), Bitcoin utilise le **modele UTXO**\n"
"(Unspent Transaction Output).\n"
"\n"
"### Account vs UTXO\n"
"\n"
"| Aspect | Account (Ethereum) | UTXO (Bitcoin) |\n"
"|--------|-------------------|----------------|\n"
"| Representation | Solde global par adresse | Ensemble de \"pieces\" non depensees |\n"
"| Analogie | Compte bancaire | Pieces et billets dans un portefeuille |\n"
"| Transaction | Debiter un compte, crediter un autre | Consommer des UTXO, en creer de nouveaux |\n"
"| Verification | Verifier le solde >= montant | Verifier que les UTXO existent et ne sont pas depenses |\n"
"| Parallelisme | Difficile (etat global) | Naturel (UTXO independants) |\n"
"| Confidentialite | Solde visible | Montants repartis en UTXO multiples |\n"
"\n"
"### Principe\n"
"\n"
"Un UTXO est une **sortie de transaction non depensee**. Chaque transaction :\n"
"1. **Consomme** un ou plusieurs UTXO existants (les *inputs*)\n"
"2. **Cree** de nouveaux UTXO (les *outputs*)\n"
"3. La somme des inputs >= somme des outputs (la difference = frais pour le mineur)\n"
"\n"
"C'est comme payer avec des billets : si vous avez un billet de 50 et devez payer 30,\n"
"vous donnez le billet de 50 et recevez 20 de monnaie.", "utxo-intro"))

UTXO_CODE = r'''import hashlib
import json
from collections import defaultdict


class UTXOSet:
    """Gestionnaire d'UTXO simplifie modelisant le coeur de Bitcoin."""

    def __init__(self):
        # UTXO = {(tx_hash, output_index): {"address": ..., "amount": ...}}
        self.utxos = {}
        self.tx_history = []

    def _tx_hash(self, tx_data):
        """Calculer le hash d'une transaction."""
        return hashlib.sha256(json.dumps(tx_data, sort_keys=True).encode()).hexdigest()

    def add_coinbase(self, address, amount, label="coinbase"):
        """Creer un UTXO de generation (recompense de minage)."""
        tx_data = {"type": "coinbase", "to": address, "amount": amount, "label": label}
        tx_hash = self._tx_hash(tx_data)
        self.utxos[(tx_hash, 0)] = {"address": address, "amount": amount}
        self.tx_history.append(tx_data)
        return tx_hash

    def get_balance(self, address):
        """Calculer le solde d'une adresse en sommant ses UTXO."""
        return sum(
            utxo["amount"] for utxo in self.utxos.values()
            if utxo["address"] == address
        )

    def get_utxos_for(self, address):
        """Lister les UTXO d'une adresse."""
        return {
            key: utxo for key, utxo in self.utxos.items()
            if utxo["address"] == address
        }

    def create_transaction(self, sender, recipient, amount, fee=0):
        """Creer une transaction UTXO.
        1. Selectionner des UTXO suffisants (coin selection)
        2. Consommer ces UTXO (inputs)
        3. Creer de nouveaux UTXO (outputs) : recipient + change
        """
        sender_utxos = self.get_utxos_for(sender)
        total_available = sum(u["amount"] for u in sender_utxos.values())

        if total_available < amount + fee:
            raise ValueError(
                f"Solde insuffisant: {total_available} < {amount + fee}"
            )

        # Coin selection (simple: on prend les UTXO un par un)
        selected = {}
        selected_total = 0
        for key, utxo in sender_utxos.items():
            selected[key] = utxo
            selected_total += utxo["amount"]
            if selected_total >= amount + fee:
                break

        # Consommer les UTXO selectionnes
        for key in selected:
            del self.utxos[key]

        # Creer les outputs
        tx_data = {
            "inputs": [{"tx": k[0][:16], "index": k[1]} for k in selected],
            "outputs": [{"address": recipient, "amount": amount}],
            "fee": fee,
        }

        change = selected_total - amount - fee
        if change > 0:
            tx_data["outputs"].append({"address": sender, "amount": change})

        tx_hash = self._tx_hash(tx_data)

        # Ajouter les nouveaux UTXO
        for i, output in enumerate(tx_data["outputs"]):
            self.utxos[(tx_hash, i)] = {
                "address": output["address"],
                "amount": output["amount"],
            }

        self.tx_history.append(tx_data)
        return tx_hash, tx_data


# Demonstration
utxo_set = UTXOSet()

# Minage initial : Alice recoit 50 BTC (coinbase)
print("MODELE UTXO - Demonstration")
print("=" * 60)

tx0 = utxo_set.add_coinbase("Alice", 50, "bloc-0-coinbase")
print(f"Coinbase -> Alice : 50 BTC (tx: {tx0[:16]}...)")

tx1 = utxo_set.add_coinbase("Alice", 25, "bloc-1-coinbase")
print(f"Coinbase -> Alice : 25 BTC (tx: {tx1[:16]}...)")
print(f"\nSolde Alice : {utxo_set.get_balance('Alice')} BTC")
print(f"UTXO d'Alice : {len(utxo_set.get_utxos_for('Alice'))} pieces")'''

cells.append(code(UTXO_CODE, "utxo-code"))

UTXO_TX_CODE = r'''# Transaction : Alice envoie 30 BTC a Bob
print("TRANSACTION : Alice -> Bob (30 BTC, frais 1 BTC)")
print("=" * 60)

tx_hash, tx_data = utxo_set.create_transaction("Alice", "Bob", 30, fee=1)

print(f"\nTx hash : {tx_hash[:32]}...")
print(f"Inputs  : {len(tx_data['inputs'])} UTXO consomme(s)")
for inp in tx_data["inputs"]:
    print(f"  <- tx {inp['tx']}... index {inp['index']}")

print(f"Outputs : {len(tx_data['outputs'])} UTXO cree(s)")
for out in tx_data["outputs"]:
    print(f"  -> {out['address']} : {out['amount']} BTC")

print(f"Frais   : {tx_data['fee']} BTC (pour le mineur)")

print(f"\nApres transaction :")
print(f"  Alice : {utxo_set.get_balance('Alice')} BTC ({len(utxo_set.get_utxos_for('Alice'))} UTXO)")
print(f"  Bob   : {utxo_set.get_balance('Bob')} BTC ({len(utxo_set.get_utxos_for('Bob'))} UTXO)")

# Bob envoie 15 BTC a Charlie
print(f"\nTRANSACTION : Bob -> Charlie (15 BTC, frais 0.5 BTC)")
tx_hash2, tx_data2 = utxo_set.create_transaction("Bob", "Charlie", 15, fee=0.5)

print(f"\nEtat final du UTXO set :")
for addr in ["Alice", "Bob", "Charlie"]:
    utxos = utxo_set.get_utxos_for(addr)
    print(f"  {addr:10s}: {utxo_set.get_balance(addr):>7.1f} BTC  ({len(utxos)} UTXO)")

print(f"\nTotal UTXO dans le systeme : {len(utxo_set.utxos)}")
print("-> Chaque UTXO est une 'piece' independante, prete a etre depensee")'''

cells.append(code(UTXO_TX_CODE, "utxo-transactions"))

cells.append(md(
"### Interpretation : Modele UTXO\n"
"\n"
"**Points cles observes** :\n"
"\n"
"1. Alice avait 2 UTXO (50 + 25 = 75 BTC). Pour envoyer 30 BTC, le systeme\n"
"   a consomme un UTXO de 50 et cree 2 nouveaux UTXO : 30 pour Bob et 19 de monnaie pour Alice.\n"
"2. Les frais (1 BTC) sont la difference entre inputs et outputs : ils vont implicitement au mineur.\n"
"3. L'UTXO de 25 BTC d'Alice reste intact : il n'a pas ete utilise.\n"
"\n"
"| Propriete | Consequence |\n"
"|-----------|-------------|\n"
"| UTXO atomiques | Impossible de depenser \"une partie\" d'un UTXO |\n"
"| Change explicite | Toute difference doit etre renvoyee comme monnaie |\n"
"| Independance | Deux transactions avec des UTXO differents sont parallelisables |\n"
"| Tracabilite | On peut remonter la chaine de propriete de chaque UTXO |", "utxo-interpretation"))

# === SECTION 2: BITCOIN SCRIPT ===
cells.append(md(
"---\n"
"\n"
"## 2. Bitcoin Script\n"
"\n"
"Bitcoin Script est un **langage a pile** (stack-based) volontairement limite :\n"
"il est **Turing-incomplet** par conception, pour eviter les boucles infinies\n"
"et garantir que la verification se termine toujours.\n"
"\n"
"### Principe\n"
"\n"
"Chaque UTXO contient un **script de verrouillage** (scriptPubKey) qui definit\n"
"les conditions pour depenser cet UTXO. Pour le depenser, l'emetteur fournit\n"
"un **script de deverrouillage** (scriptSig) qui satisfait ces conditions.\n"
"\n"
"```\n"
"scriptSig + scriptPubKey -> execution sur la pile -> resultat TRUE/FALSE\n"
"```\n"
"\n"
"### Opcodes principaux\n"
"\n"
"| Opcode | Effet sur la pile | Description |\n"
"|--------|------------------|-------------|\n"
"| `OP_DUP` | a -> a a | Duplique le sommet de la pile |\n"
"| `OP_HASH160` | a -> HASH160(a) | RIPEMD160(SHA256(a)) |\n"
"| `OP_EQUAL` | a b -> (a==b) | Egalite, pousse TRUE/FALSE |\n"
"| `OP_EQUALVERIFY` | a b -> (vide si OK) | Egalite + echec si FALSE |\n"
"| `OP_CHECKSIG` | sig pubkey -> TRUE/FALSE | Verifie une signature ECDSA |\n"
"| `OP_CHECKMULTISIG` | ... -> TRUE/FALSE | Verifie M signatures sur N cles |\n"
"| `OP_IF` / `OP_ELSE` / `OP_ENDIF` | Conditionnel | Branchement selon le sommet |\n"
"| `OP_RETURN` | - | Marque l'output comme non-depensable |\n"
"| `OP_CHECKLOCKTIMEVERIFY` | n -> n | Verifie que le timelock est atteint |", "script-intro"))

SCRIPT_INTERP_CODE = r'''import hashlib


def hash160(data):
    """HASH160 = RIPEMD160(SHA256(data)), utilise par Bitcoin pour les adresses."""
    sha = hashlib.sha256(data).digest()
    ripemd = hashlib.new("ripemd160", sha).digest()
    return ripemd


class BitcoinScriptInterpreter:
    """Mini-interpreteur Bitcoin Script en Python.
    Supporte un sous-ensemble des opcodes reels.
    """

    def __init__(self):
        self.stack = []
        self.opcodes = {
            "OP_DUP":          self._op_dup,
            "OP_HASH160":      self._op_hash160,
            "OP_EQUAL":        self._op_equal,
            "OP_EQUALVERIFY":  self._op_equalverify,
            "OP_VERIFY":       self._op_verify,
            "OP_CHECKSIG":     self._op_checksig,
            "OP_ADD":          self._op_add,
            "OP_SUB":          self._op_sub,
            "OP_TRUE":         self._op_true,
            "OP_DROP":         self._op_drop,
            "OP_2DUP":         self._op_2dup,
            "OP_SWAP":         self._op_swap,
        }

    def _op_dup(self):
        """Duplique le sommet de la pile."""
        if len(self.stack) < 1:
            raise RuntimeError("Pile vide pour OP_DUP")
        self.stack.append(self.stack[-1])

    def _op_hash160(self):
        """RIPEMD160(SHA256(top))."""
        val = self.stack.pop()
        if isinstance(val, str):
            val = val.encode()
        self.stack.append(hash160(val))

    def _op_equal(self):
        """Compare les deux elements du sommet."""
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a == b)

    def _op_equalverify(self):
        """EQUAL + VERIFY : echoue si pas egaux."""
        self._op_equal()
        if not self.stack.pop():
            raise RuntimeError("OP_EQUALVERIFY echoue")

    def _op_verify(self):
        """Echoue si le sommet est FALSE."""
        if not self.stack.pop():
            raise RuntimeError("OP_VERIFY echoue")

    def _op_checksig(self):
        """Verification simplifiee de signature (simulee)."""
        pubkey = self.stack.pop()
        signature = self.stack.pop()
        # Simulation : la signature est valide si elle contient
        # le hash de la cle publique (simplifie pour la pedagogie)
        if isinstance(pubkey, str):
            pubkey = pubkey.encode()
        expected_sig = hashlib.sha256(pubkey).hexdigest()[:16]
        is_valid = (signature == expected_sig)
        self.stack.append(is_valid)

    def _op_add(self):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a + b)

    def _op_sub(self):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a - b)

    def _op_true(self):
        self.stack.append(True)

    def _op_drop(self):
        self.stack.pop()

    def _op_2dup(self):
        if len(self.stack) < 2:
            raise RuntimeError("Pile insuffisante pour OP_2DUP")
        self.stack.append(self.stack[-2])
        self.stack.append(self.stack[-2])

    def _op_swap(self):
        self.stack[-1], self.stack[-2] = self.stack[-2], self.stack[-1]

    def execute(self, script, verbose=True):
        """Executer un script Bitcoin (liste d'opcodes et donnees)."""
        self.stack = []
        if verbose:
            print(f"Script : {script}")
            print("-" * 50)

        for item in script:
            if item in self.opcodes:
                if verbose:
                    print(f"  {item:20s}", end="")
                self.opcodes[item]()
            else:
                if verbose:
                    display = item if not isinstance(item, bytes) else item.hex()[:16] + "..."
                    print(f"  PUSH {str(display):14s}", end="")
                self.stack.append(item)

            if verbose:
                stack_display = []
                for s in self.stack:
                    if isinstance(s, bytes):
                        stack_display.append(s.hex()[:12] + "...")
                    else:
                        stack_display.append(str(s))
                print(f"  pile: {stack_display}")

        return len(self.stack) > 0 and self.stack[-1]


# Demonstration : script arithmetique simple
interp = BitcoinScriptInterpreter()

print("MINI-INTERPRETEUR BITCOIN SCRIPT")
print("=" * 60)
print()
print("--- Script 1 : Verification arithmetique (2 + 3 == 5) ---")
result = interp.execute([2, 3, "OP_ADD", 5, "OP_EQUAL"])
print(f"Resultat : {result}")
print()'''

cells.append(code(SCRIPT_INTERP_CODE, "script-interpreter"))

P2PKH_CODE = r'''# P2PKH : Pay-to-Public-Key-Hash
# Le script de verrouillage le plus courant de Bitcoin
# ~95% des transactions Bitcoin utilisent ce format

print("--- Script P2PKH (Pay-to-Public-Key-Hash) ---")
print()

# Simuler une cle publique et son hash
pubkey = "02abc123def456...alice_public_key"
pubkey_hash = hash160(pubkey.encode())

# La signature simulee (en realite : ECDSA sur la transaction)
signature = hashlib.sha256(pubkey.encode()).hexdigest()[:16]

print(f"Cle publique  : {pubkey[:30]}...")
print(f"HASH160(pubkey): {pubkey_hash.hex()}")
print(f"Signature     : {signature}")
print()

# Script complet P2PKH :
# scriptSig (deverrouillage) : <signature> <pubkey>
# scriptPubKey (verrouillage) : OP_DUP OP_HASH160 <pubkey_hash> OP_EQUALVERIFY OP_CHECKSIG

# En Bitcoin, on concatene scriptSig + scriptPubKey
full_script = [
    # --- scriptSig (fourni par celui qui depense) ---
    signature,           # signature ECDSA
    pubkey,              # cle publique
    # --- scriptPubKey (inscrit dans l'UTXO) ---
    "OP_DUP",            # dupliquer la cle publique
    "OP_HASH160",        # hasher la copie
    pubkey_hash,         # hash attendu (stocke dans l'UTXO)
    "OP_EQUALVERIFY",    # verifier que les hash correspondent
    "OP_CHECKSIG",       # verifier la signature
]

print("Execution du script P2PKH :")
print("(scriptSig + scriptPubKey concatenes)")
print()
interp2 = BitcoinScriptInterpreter()
result = interp2.execute(full_script)
print(f"\nResultat : {result}")
print("-> La transaction est autorisee : le detenteur de la cle privee peut depenser l'UTXO")'''

cells.append(code(P2PKH_CODE, "p2pkh-code"))

cells.append(md(
"### Interpretation : Bitcoin Script\n"
"\n"
"Le script P2PKH execute les etapes suivantes sur la pile :\n"
"\n"
"| Etape | Operation | Pile (sommet a droite) |\n"
"|-------|-----------|----------------------|\n"
"| 1 | PUSH signature | [sig] |\n"
"| 2 | PUSH pubkey | [sig, pubkey] |\n"
"| 3 | OP_DUP | [sig, pubkey, pubkey] |\n"
"| 4 | OP_HASH160 | [sig, pubkey, hash(pubkey)] |\n"
"| 5 | PUSH expected_hash | [sig, pubkey, hash(pubkey), expected_hash] |\n"
"| 6 | OP_EQUALVERIFY | [sig, pubkey] (echoue si hash different) |\n"
"| 7 | OP_CHECKSIG | [TRUE] (signature valide) |\n"
"\n"
"**Pourquoi Turing-incomplet ?**\n"
"- Pas de boucles -> execution garantie en temps fini\n"
"- Pas de memoire persistante -> pas d'etat entre transactions\n"
"- Securite maximale : on ne peut pas creer de contrat qui boucle indefiniment\n"
"- Contrepartie : impossible d'ecrire des contrats complexes comme sur Ethereum", "script-interpretation"))

# === SECTION 3: CREATION DE TRANSACTIONS ===
cells.append(md(
"---\n"
"\n"
"## 3. Construction de transactions Bitcoin\n"
"\n"
"Une transaction Bitcoin brute est une structure binaire avec un format precis.\n"
"Cette section montre la construction manuelle d'une transaction, puis\n"
"l'utilisation optionnelle de `python-bitcoinlib` pour la version complete avec signature.",
"tx-intro"))

RAW_TX_CODE = '''import hashlib
import struct
import time


class RawTransaction:
    """Construction manuelle d'une transaction Bitcoin brute (simplifiee)."""

    def __init__(self, version=1):
        self.version = version
        self.inputs = []
        self.outputs = []
        self.locktime = 0  # 0 = pas de timelock

    def add_input(self, prev_tx_hash, prev_output_index, script_sig=b""):
        """Ajouter un input (reference a un UTXO existant)."""
        self.inputs.append({
            "prev_tx": bytes.fromhex(prev_tx_hash),
            "prev_index": prev_output_index,
            "script_sig": script_sig,
            "sequence": 0xFFFFFFFF,  # pas de RBF
        })

    def add_output(self, amount_satoshis, script_pubkey=b""):
        """Ajouter un output (nouveau UTXO)."""
        self.outputs.append({
            "amount": amount_satoshis,
            "script_pubkey": script_pubkey,
        })

    def serialize(self):
        """Serialiser la transaction au format binaire Bitcoin."""
        raw = b""
        # Version (4 bytes, little-endian)
        raw += struct.pack("<I", self.version)

        # Nombre d'inputs (varint)
        raw += bytes([len(self.inputs)])
        for inp in self.inputs:
            raw += inp["prev_tx"][::-1]  # hash en little-endian
            raw += struct.pack("<I", inp["prev_index"])
            raw += bytes([len(inp["script_sig"])]) + inp["script_sig"]
            raw += struct.pack("<I", inp["sequence"])

        # Nombre d'outputs (varint)
        raw += bytes([len(self.outputs)])
        for out in self.outputs:
            raw += struct.pack("<q", out["amount"])  # montant en satoshis
            raw += bytes([len(out["script_pubkey"])]) + out["script_pubkey"]

        # Locktime (4 bytes)
        raw += struct.pack("<I", self.locktime)
        return raw

    def txid(self):
        """Calculer le txid (double SHA-256 de la transaction serialisee)."""
        raw = self.serialize()
        return hashlib.sha256(hashlib.sha256(raw).digest()).hexdigest()


# Construire une transaction manuellement
tx = RawTransaction(version=2)

# Input : reference a un UTXO fictif
prev_tx = "a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2"
tx.add_input(prev_tx, 0)

# Output 1 : envoyer 0.5 BTC (50,000,000 satoshis) a Bob
bob_script = b"\\x76\\xa9" + hash160(b"bob_pubkey") + b"\\x88\\xac"  # P2PKH
tx.add_output(50_000_000, bob_script)

# Output 2 : monnaie rendue a Alice (0.49 BTC)
alice_script = b"\\x76\\xa9" + hash160(b"alice_pubkey") + b"\\x88\\xac"
tx.add_output(49_000_000, alice_script)

# Frais implicites : 0.01 BTC (1,000,000 satoshis)
raw = tx.serialize()

print("TRANSACTION BITCOIN BRUTE")
print("=" * 60)
print(f"Version  : {tx.version}")
print(f"Inputs   : {len(tx.inputs)}")
print(f"Outputs  : {len(tx.outputs)}")
print(f"  Output 0 (Bob)   : {tx.outputs[0]['amount']:>12,} satoshis (0.5 BTC)")
print(f"  Output 1 (Alice) : {tx.outputs[1]['amount']:>12,} satoshis (0.49 BTC)")
print(f"  Frais implicites : {1_000_000:>12,} satoshis (0.01 BTC)")
print(f"Locktime : {tx.locktime}")
print(f"\nTaille brute  : {len(raw)} octets")
print(f"TxID          : {tx.txid()}")
print(f"Hex (debut)   : {raw[:32].hex()}")
print(f"\nStructure : [version:4][nb_inputs:1][inputs...][nb_outputs:1][outputs...][locktime:4]")'''

cells.append(code(RAW_TX_CODE, "raw-tx-code"))

BITCOINLIB_CODE = r'''# Utilisation de python-bitcoinlib (optionnel)
# Cette bibliotheque fournit les types Bitcoin natifs

try:
    import bitcoin
    from bitcoin.core import (
        CMutableTransaction, CMutableTxIn, CMutableTxOut,
        COutPoint, lx
    )
    from bitcoin.core.script import (
        CScript, OP_DUP, OP_HASH160, OP_EQUALVERIFY, OP_CHECKSIG
    )
    from bitcoin.wallet import CBitcoinSecret, P2PKHBitcoinAddress

    # Selectionner le reseau testnet
    bitcoin.SelectParams("testnet")

    # Generer une cle privee
    secret_bytes = hashlib.sha256(b"cle_demo_ne_pas_utiliser_en_production").digest()
    secret = CBitcoinSecret.from_secret_bytes(secret_bytes)
    address = P2PKHBitcoinAddress.from_pubkey(secret.pub)

    print("PYTHON-BITCOINLIB")
    print("=" * 60)
    print(f"Cle privee (WIF) : {secret}")
    print(f"Cle publique     : {secret.pub.hex()}")
    print(f"Adresse (testnet): {address}")
    print()

    # Creer une transaction avec la bibliotheque
    txin = CMutableTxIn(
        COutPoint(lx("a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2"), 0)
    )

    # Script P2PKH standard
    script_pubkey = CScript([
        OP_DUP, OP_HASH160,
        bitcoin.core.Hash160(secret.pub),
        OP_EQUALVERIFY, OP_CHECKSIG
    ])
    txout = CMutableTxOut(50_000_000, script_pubkey)

    tx = CMutableTransaction([txin], [txout])
    print(f"Transaction creee avec python-bitcoinlib")
    print(f"  Taille : {len(tx.serialize())} octets")
    print(f"  Script : {script_pubkey.hex()}")

except ImportError:
    print("python-bitcoinlib non installe.")
    print("Pour l'installer : pip install python-bitcoinlib")
    print()
    print("Les sections precedentes utilisent du Python pur et ne")
    print("necessitent aucune dependance externe.")
    print("python-bitcoinlib ajoute les types natifs Bitcoin (CTransaction,")
    print("CScript, etc.) et la gestion complete des signatures ECDSA.")'''

cells.append(code(BITCOINLIB_CODE, "bitcoinlib-code"))

cells.append(md(
"### Interpretation : Transactions Bitcoin\n"
"\n"
"La structure d'une transaction Bitcoin est remarquablement simple :\n"
"\n"
"```\n"
"+----------+--------+--------------------+--------+---------------------+----------+\n"
"| Version  | Nb In  | Inputs             | Nb Out | Outputs             | Locktime |\n"
"| 4 bytes  | varint | (prev_tx + script) | varint | (amount + script)   | 4 bytes  |\n"
"+----------+--------+--------------------+--------+---------------------+----------+\n"
"```\n"
"\n"
"**Points cles** :\n"
"- Les montants sont en **satoshis** (1 BTC = 100 000 000 satoshis)\n"
"- Les frais ne sont pas explicites : c'est la difference entre inputs et outputs\n"
"- Le `txid` est le double SHA-256 de la transaction serialisee\n"
"- `locktime` permet de retarder la validite d'une transaction", "tx-interpretation"))

# === SECTION 4: SCRIPTS AVANCES ===
cells.append(md(
"---\n"
"\n"
"## 4. Scripts avances\n"
"\n"
"Bitcoin Script permet des schemas de transaction plus sophistiques que le simple P2PKH.\n"
"Ces mecanismes sont la base des \"contrats\" Bitcoin, bien plus limites que les smart contracts\n"
"Ethereum mais suffisants pour de nombreux cas d'usage.", "advanced-intro"))

MULTISIG_CODE = r'''# === MULTISIG (2-of-3) ===
# Necessite 2 signatures parmi 3 cles autorisees
# Utilise pour : coffres d'entreprise, escrow, wallets partages

print("SCRIPTS AVANCES")
print("=" * 60)
print()
print("--- 4.1 Multisig (2-of-3) ---")
print()

# Cles publiques des 3 signataires
keys = {
    "Alice": hashlib.sha256(b"alice_key").hexdigest()[:40],
    "Bob":   hashlib.sha256(b"bob_key").hexdigest()[:40],
    "Carol": hashlib.sha256(b"carol_key").hexdigest()[:40],
}

# Script de verrouillage multisig
multisig_script = [
    "OP_2",              # M = 2 signatures requises
    keys["Alice"],       # cle publique 1
    keys["Bob"],         # cle publique 2
    keys["Carol"],       # cle publique 3
    "OP_3",              # N = 3 cles au total
    "OP_CHECKMULTISIG",  # verifier M-of-N
]

print("scriptPubKey (verrouillage) :")
for item in multisig_script:
    if item.startswith("OP_"):
        print(f"  {item}")
    else:
        # Trouver le nom de la cle
        name = [k for k, v in keys.items() if v == item][0]
        print(f"  <{name}_pubkey> ({item[:16]}...)")

print()
print("scriptSig (deverrouillage, signe par Alice et Carol) :")
print("  OP_0              (bug historique de Bitcoin)")
print("  <sig_Alice>")
print("  <sig_Carol>")
print()
print("-> 2 signatures sur 3 suffisent pour depenser l'UTXO")
print("-> Cas d'usage : Alice + Bob = depense normale")
print("                 Alice + Carol = si Bob est indisponible")
print("                 Bob + Carol = arbitrage sans Alice")'''

cells.append(code(MULTISIG_CODE, "multisig-code"))

TIMELOCK_CODE = r'''# === TIMELOCK (CLTV et CSV) ===
# CLTV = CheckLockTimeVerify : verrouillage jusqu'a un bloc ou une date
# CSV  = CheckSequenceVerify : verrouillage relatif (N blocs apres confirmation)

import time

print("--- 4.2 Timelock (CLTV / CSV) ---")
print()

# Hauteur de bloc actuelle simulee
current_block = 840_000  # Approximation avril 2024
current_time = int(time.time())

# CLTV : ne peut pas etre depense avant le bloc 850,000
cltv_script = [
    850_000,                       # hauteur de bloc cible
    "OP_CHECKLOCKTIMEVERIFY",      # echoue si bloc < 850,000
    "OP_DROP",                     # retirer la valeur de la pile
    # ... suivi du script P2PKH normal
    "OP_DUP", "OP_HASH160", "<pubkey_hash>", "OP_EQUALVERIFY", "OP_CHECKSIG"
]

# CSV : ne peut pas etre depense avant 144 blocs (~24h) apres confirmation
csv_blocks = 144  # ~24 heures
csv_script = [
    csv_blocks,                    # nombre de blocs relatif
    "OP_CHECKSEQUENCEVERIFY",      # echoue si sequence < 144
    "OP_DROP",
    "OP_DUP", "OP_HASH160", "<pubkey_hash>", "OP_EQUALVERIFY", "OP_CHECKSIG"
]

print("CLTV (CheckLockTimeVerify) - Timelock absolu :")
print(f"  Bloc actuel      : {current_block:,}")
print(f"  Bloc cible        : 850,000")
remaining = 850_000 - current_block
print(f"  Blocs restants    : {remaining:,} (~{remaining * 10 // 60} heures)")
if current_block < 850_000:
    print("  Status            : VERROUILLE")
else:
    print("  Status            : DEVERROUILLE")
print()
print("CSV (CheckSequenceVerify) - Timelock relatif :")
print(f"  Delai requis      : {csv_blocks} blocs (~24 heures)")
print(f"  Usage typique     : delai de securite apres depot")
print()

print("Comparaison des timelocks :")
fmt = "  {:<10} {:<20} {}"
print(fmt.format("Type", "Reference", "Usage courant"))
print(fmt.format("CLTV", "Bloc ou timestamp", "Heritage, paris, echeances"))
print(fmt.format("CSV", "Blocs relatifs", "Lightning Network, securite"))
print(fmt.format("nLocktime", "Champ de la tx", "Transactions differees"))'''

cells.append(code(TIMELOCK_CODE, "timelock-code"))

P2SH_CODE = r'''# === P2SH (Pay-to-Script-Hash) ===
# BIP 16 : au lieu de mettre le script complet dans l'output,
# on met seulement son hash. Le script complet est revele au moment
# de depenser.

print("--- 4.3 P2SH (Pay-to-Script-Hash) ---")
print()

# Le script multisig 2-of-3 est long et couteux en espace
# Avec P2SH, on le remplace par son hash

redeem_script = "OP_2 <Alice> <Bob> <Carol> OP_3 OP_CHECKMULTISIG"
redeem_hash = hash160(redeem_script.encode())

print("Sans P2SH (multisig brut dans scriptPubKey) :")
print(f"  scriptPubKey : OP_2 <pk1> <pk2> <pk3> OP_3 OP_CHECKMULTISIG")
print(f"  Taille script : ~{len(redeem_script)} octets")
print(f"  -> L'expediteur paie pour la complexite du script")
print()

print("Avec P2SH (hash du script dans scriptPubKey) :")
print(f"  scriptPubKey : OP_HASH160 {redeem_hash.hex()[:20]}... OP_EQUAL")
print(f"  Taille script : ~23 octets (toujours la meme)")
print(f"  -> L'expediteur paie un cout fixe, peu importe la complexite")
print()

print("Pour depenser (scriptSig) :")
print(f"  OP_0 <sig_Alice> <sig_Bob> <redeem_script_complet>")
print(f"  -> Le script complet est revele seulement au moment de depenser")
print(f"  -> Le destinataire paie la complexite")
print()

print("Avantages de P2SH :")
print("  1. Adresses P2SH commencent par '3' (vs '1' pour P2PKH)")
print("  2. Taille fixe de l'output, quelle que soit la complexite du script")
print("  3. La complexite est cachee jusqu'a la depense")
print("  4. Le destinataire choisit les conditions de depense")'''

cells.append(code(P2SH_CODE, "p2sh-code"))

cells.append(md(
"### Interpretation : Scripts avances\n"
"\n"
"| Type | Complexite | Cas d'usage | Adresse |\n"
"|------|-----------|-------------|--------|\n"
"| **P2PKH** | Simple | Paiement standard | Commence par `1` |\n"
"| **Multisig** | M-of-N | Coffres partages, escrow | Integre dans P2SH |\n"
"| **CLTV** | Timelock absolu | Heritage, paris, echeances | Integre dans P2SH |\n"
"| **CSV** | Timelock relatif | Lightning Network, securite | Integre dans P2SH |\n"
"| **P2SH** | Hash de script | Encapsule tout script complexe | Commence par `3` |\n"
"| **P2WSH** | SegWit | Version moderne de P2SH | Commence par `bc1` |\n"
"\n"
"> **Note** : Depuis 2021, **Taproot** (BIP 340-342) ajoute les signatures Schnorr et les\n"
"> arbres MAST, permettant des scripts encore plus flexibles et confidentiels.\n"
"> Les adresses Taproot commencent par `bc1p`.", "advanced-interpretation"))

# === SECTION 5: BITCOIN vs ETHEREUM ===
cells.append(md(
"---\n"
"\n"
"## 5. Bitcoin vs Ethereum : deux philosophies\n"
"\n"
"Bitcoin et Ethereum representent deux approches fondamentalement differentes\n"
"de la programmabilite blockchain.\n"
"\n"
"### Comparaison architecturale\n"
"\n"
"| Aspect | Bitcoin | Ethereum |\n"
"|--------|---------|----------|\n"
"| **Modele d'etat** | UTXO | Account |\n"
"| **Langage** | Bitcoin Script (pile) | Solidity/Vyper (Turing-complet) |\n"
"| **Turing-completude** | Non (pas de boucles) | Oui (avec gas limit) |\n"
"| **Etat persistent** | Non (stateless) | Oui (storage) |\n"
"| **Execution** | Verification (valide/invalide) | Computation (execution complete) |\n"
"| **Gas/Frais** | Par octet de transaction | Par instruction executee |\n"
"| **Expressivite** | Limitee (conditions de depense) | Maximale (programmes arbitraires) |\n"
"| **Securite** | Minimale surface d'attaque | Surface d'attaque large (reentrancy, etc.) |\n"
"\n"
"### Avantages de Bitcoin Script\n"
"\n"
"1. **Securite par restriction** : impossible de creer de bugs complexes\n"
"2. **Verification rapide** : l'execution se termine toujours en temps borne\n"
"3. **Confidentialite** : le script n'est revele qu'a la depense (P2SH)\n"
"4. **Previsibilite des frais** : proportionnels a la taille, pas a la complexite\n"
"\n"
"### Avantages d'Ethereum/Solidity\n"
"\n"
"1. **Expressivite** : tout algorithme peut etre encode\n"
"2. **Etat persistent** : le contrat \"se souvient\" entre les appels\n"
"3. **Composabilite** : les contrats peuvent s'appeler entre eux (DeFi)\n"
"4. **Ecosysteme** : outils, librairies, standards (ERC-20, ERC-721)\n"
"\n"
"### Convergence recente\n"
"\n"
"- **Bitcoin** : Taproot (2021) ajoute plus de flexibilite, Ordinals/Inscriptions\n"
"  poussent les limites du script\n"
"- **Ethereum** : les L2 (rollups) utilisent des preuves de validite similaires\n"
"  a l'approche Bitcoin (verification > computation)\n"
"- **Les deux** : convergent vers un modele ou la L1 **verifie** et les L2 **executent**",
"comparison"))

# === SECTION 6: EXERCICE ===
cells.append(md(
"---\n"
"\n"
"## 6. Exercice : Escrow avec timelock\n"
"\n"
"Implementez un systeme d'escrow (tiers de confiance) en utilisant les concepts\n"
"de Bitcoin Script vus dans ce notebook.\n"
"\n"
"### Scenario\n"
"\n"
"Alice achete un produit a Bob. L'argent est verrouille dans un escrow :\n"
"- **Cas normal** : Alice ET Bob signent pour liberer les fonds vers Bob\n"
"- **Litige** : Alice ET Carol (arbitre) signent pour rembourser Alice\n"
"- **Timeout** : apres 1000 blocs sans action, Bob peut recuperer les fonds seul\n"
"\n"
"### Instructions\n"
"\n"
"1. Completez la classe `TimelockEscrow`\n"
"2. Le script doit combiner multisig et timelock\n"
"3. Testez les trois scenarios (normal, litige, timeout)", "exercise-intro"))

EXERCISE_CODE = r'''import hashlib
import time


class TimelockEscrow:
    """Escrow avec timelock combinant multisig et CLTV.

    Regles :
    - Alice + Bob : liberation immediate vers Bob
    - Alice + Carol (arbitre) : remboursement vers Alice
    - Bob seul apres timeout : recuperation par Bob
    """

    def __init__(self, alice_pubkey, bob_pubkey, carol_pubkey,
                 amount, timeout_blocks=1000):
        self.alice = alice_pubkey
        self.bob = bob_pubkey
        self.carol = carol_pubkey
        self.amount = amount
        self.timeout_blocks = timeout_blocks
        self.creation_block = 0
        self.is_spent = False

    def get_redeem_script(self):
        """Construire le script de verrouillage.
        TODO: Retourner une liste representant le script Bitcoin.

        Le script doit implementer :
        - OP_IF : branche multisig 2-of-3 (Alice, Bob, Carol)
        - OP_ELSE : branche timeout (Bob seul apres N blocs)
        - OP_ENDIF

        Hint: utilisez le format [
            "OP_IF",
            "OP_2", alice, bob, carol, "OP_3", "OP_CHECKMULTISIG",
            "OP_ELSE",
            timeout_blocks, "OP_CHECKLOCKTIMEVERIFY", "OP_DROP",
            bob, "OP_CHECKSIG",
            "OP_ENDIF"
        ]
        """
        raise NotImplementedError("Implementez le script de verrouillage")

    def release_to_bob(self, alice_sig, bob_sig):
        """Cas normal : Alice et Bob signent pour liberer.
        TODO:
        1. Verifier que l'escrow n'est pas deja depense
        2. Verifier les deux signatures (simulees)
        3. Marquer comme depense et retourner le montant
        """
        raise NotImplementedError("Implementez la liberation vers Bob")

    def refund_to_alice(self, alice_sig, carol_sig):
        """Litige : Alice et Carol (arbitre) remboursent Alice.
        TODO:
        1. Verifier que l'escrow n'est pas deja depense
        2. Verifier les signatures d'Alice et Carol
        3. Marquer comme depense et retourner le montant
        """
        raise NotImplementedError("Implementez le remboursement")

    def timeout_release(self, bob_sig, current_block):
        """Timeout : Bob recupere apres N blocs.
        TODO:
        1. Verifier que l'escrow n'est pas deja depense
        2. Verifier que current_block >= creation_block + timeout_blocks
        3. Verifier la signature de Bob
        4. Marquer comme depense et retourner le montant
        """
        raise NotImplementedError("Implementez la liberation par timeout")


# Test (decommentez apres implementation)
# escrow = TimelockEscrow(
#     alice_pubkey="alice_pub",
#     bob_pubkey="bob_pub",
#     carol_pubkey="carol_pub",
#     amount=1.5,  # BTC
#     timeout_blocks=1000
# )
# escrow.creation_block = 840_000
#
# print("Script de verrouillage :")
# for item in escrow.get_redeem_script():
#     print(f"  {item}")
#
# # Cas 1 : liberation normale
# result = escrow.release_to_bob("alice_sig", "bob_sig")
# print(f"\nLiberation vers Bob : {result} BTC")
#
# # Cas 2 : timeout (reinitialiser pour tester)
# escrow.is_spent = False
# result = escrow.timeout_release("bob_sig", 841_001)
# print(f"Timeout vers Bob : {result} BTC")

print("Exercice : completez la classe TimelockEscrow ci-dessus")
print("puis decommentez le code de test.")'''

cells.append(code(EXERCISE_CODE, "exercise-code"))

# === SECTION 7: RESUME ===
cells.append(md(
"---\n"
"\n"
"## 7. Resume\n"
"\n"
"| Concept | Description | Implementation |\n"
"|---------|-------------|----------------|\n"
"| **UTXO** | Modele de pieces non depensees | Classe `UTXOSet` avec coin selection |\n"
"| **Bitcoin Script** | Langage a pile, Turing-incomplet | Interpreteur avec 12 opcodes |\n"
"| **P2PKH** | Paiement standard a un hash de cle publique | DUP + HASH160 + EQUALVERIFY + CHECKSIG |\n"
"| **Transaction brute** | Structure binaire serialisee | Version + inputs + outputs + locktime |\n"
"| **Multisig** | M-of-N signatures requises | 2-of-3 pour coffres partages |\n"
"| **Timelock** | Verrouillage temporel (CLTV/CSV) | Bloc absolu ou relatif |\n"
"| **P2SH** | Hash du script dans l'output | Taille fixe, complexite cachee |\n"
"\n"
"### Points cles\n"
"\n"
"- Le modele UTXO offre un **parallelisme naturel** et une meilleure confidentialite que le modele Account\n"
"- Bitcoin Script est **volontairement limite** pour maximiser la securite\n"
"- Les scripts avances (multisig, timelock, P2SH) couvrent la majorite des besoins en conditions de depense\n"
"- La philosophie de Bitcoin est **verification**, celle d'Ethereum est **computation**\n"
"\n"
"---\n"
"\n"
"**Notebook suivant** : [SC-21-Move-Sui](SC-21-Move-Sui.ipynb) - Le langage Move et la blockchain Sui",
"summary"))

# === BUILD NOTEBOOK ===
notebook = {
    "cells": cells,
    "metadata": {
        "kernelspec": {
            "display_name": "Python 3",
            "language": "python",
            "name": "python3"
        },
        "language_info": {
            "codemirror_mode": {"name": "ipython", "version": 3},
            "file_extension": ".py",
            "mimetype": "text/x-python",
            "name": "python",
            "nbconvert_exporter": "python",
            "pygments_lexer": "ipython3",
            "version": "3.10.0"
        }
    },
    "nbformat": 4,
    "nbformat_minor": 5
}

output_dir = os.path.join(
    "d:", os.sep, "CoursIA", "MyIA.AI.Notebooks", "SymbolicAI",
    "SmartContracts", "05-Alternative-Chains"
)
os.makedirs(output_dir, exist_ok=True)

output_path = os.path.join(output_dir, "SC-20-Bitcoin-Scripting.ipynb")
with open(output_path, 'w', encoding='utf-8', newline='\n') as f:
    json.dump(notebook, f, ensure_ascii=False, indent=1)
    f.write('\n')

print(f"Notebook cree : {output_path}")
print(f"Cellules : {len(cells)} ({sum(1 for c in cells if c['cell_type']=='markdown')} md + {sum(1 for c in cells if c['cell_type']=='code')} code)")

# Verify format
for i, cell in enumerate(cells):
    src = cell['source']
    if isinstance(src, str):
        print(f"  ISSUE cell {i}: bare string")
    elif isinstance(src, list) and len(src) == 1 and '\n' in src[0]:
        print(f"  ISSUE cell {i}: single-string with newlines")
print("Format OK" if all(isinstance(c['source'], list) for c in cells) else "FORMAT ISSUES")
