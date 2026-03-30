"""
Script d'itération pour ajuster les paramètres si les backtests ne sont pas bons.

Usage: python iterate_params.py

Si un backtest échoue (Sharpe < attendu - 0.2), ce script propose:
1. De nouvelles valeurs de paramètres à tester
2. Les commandes pour lancer les nouveaux backtests
"""

# Paramètres actuels et alternatives pour chaque stratégie

ITERATIONS = {
    'BTC-MACD-ADX': {
        'project_id': 19898232,
        'params_actuels': {
            'AdxWindowPeriod': 80,
            'AdxLowerPercentile': 5,
            'AdxUpperPercentile': 85
        },
        'alternatives': [
            {
                'name': 'Plus conservateur (moins de trades)',
                'AdxWindowPeriod': 100,
                'AdxLowerPercentile': 10,
                'AdxUpperPercentile': 90,
                'raison': 'Si trop de whipsaw, augmenter les filtres'
            },
            {
                'name': 'Plus agressif (plus de trades)',
                'AdxWindowPeriod': 60,
                'AdxLowerPercentile': 5,
                'AdxUpperPercentile': 80,
                'raison': 'Si trop peu de trades, réduire filtres'
            },
            {
                'name': 'ADX fixe (pas adaptatif)',
                'AdxWindowPeriod': None,  # Désactive l'approche adaptative
                'AdxLowerPercentile': 25,  # Seuil fixe ADX
                'AdxUpperPercentile': 20,  # Seuil fixe ADX
                'raison': 'Simplifier, enlever la logique adaptative'
            }
        ],
        'sharpe_attendu': 0.35,
        'sharpe_min_acceptable': 0.15
    },
    'ETF-Pairs': {
        'project_id': 19865767,
        'params_actuels': {
            'half_life_max': 30,
            'z_exit_threshold': 0.0,
            'stop_loss_per_leg': False
        },
        'alternatives': [
            {
                'name': 'HL filter plus strict',
                'half_life_max': 20,
                'raison': 'Si pairs trop instables'
            },
            {
                'name': 'HL filter plus large',
                'half_life_max': 45,
                'raison': 'Si pas assez de paires'
            },
            {
                'name': 'Ajouter spread-level stop',
                'stop_loss_spread_sigma': 2.5,
                'raison': 'Pour limiter les pertes sur divergence'
            }
        ],
        'sharpe_attendu': 0.5,
        'sharpe_min_acceptable': 0.2
    },
    'Sector-Momentum': {
        'project_id': 20216980,
        'params_actuels': {
            'vix_threshold': 25,
            'leverage': 1.5
        },
        'alternatives': [
            {
                'name': 'VIX filter plus strict',
                'vix_threshold': 20,
                'raison': 'Si trop de whipsaw en haute vol'
            },
            {
                'name': 'VIX filter plus large',
                'vix_threshold': 30,
                'raison': 'Si trop peu de rebalancements'
            },
            {
                'name': 'Leverage 1.0x',
                'leverage': 1.0,
                'raison': 'Si Max DD trop élevé'
            }
        ],
        'sharpe_attendu': 0.9,
        'sharpe_min_acceptable': 0.6
    }
}

def analyze_results(sharpe_real, sharpe_expected, strategy_name):
    """Analyze results and suggest next steps"""
    diff = sharpe_real - sharpe_expected

    print(f"\n📊 Analyse {strategy_name}")
    print(f"   Sharpe attendu: {sharpe_expected}")
    print(f"   Sharpe réel: {sharpe_real}")
    print(f"   Écart: {diff:+.3f}")

    if abs(diff) <= 0.2:
        print(f"   ✅ EXCELLENT - Prédiction confirmée!")
        return None
    elif diff > 0.2:
        print(f"   🎉 SURPRISE POSITIVE - Meilleur que prévu!")
        return None
    elif diff < -0.5:
        print(f"   ❌ ÉCHEC - Nettement pire que prévu")
        print(f"   → Tester les alternatives...")
        return 'iterate'
    elif diff < -0.2:
        print(f"   ⚠️ SOUS-PERFORMANCE - Un peu sous les attentes")
        print(f"   → Peut-être acceptable, monitorer...")
        return 'monitor'
    else:
        print(f"   ✅ ACCEPTABLE - Dans la marge d'erreur")
        return None

def print_alternatives(strategy_name, alternatives):
    """Print alternative parameters to test"""
    print(f"\n🔄 Alternatives pour {strategy_name}:")
    print()

    for i, alt in enumerate(alternatives, 1):
        print(f"{i}. {alt['name']}")
        print(f"   Paramètres: {alt}")
        print(f"   Raison: {alt['raison']}")
        print()

def generate_code_snippet(strategy_name, project_id, new_params):
    """Generate code snippet for updating parameters"""
    if strategy_name == 'BTC-MACD-ADX':
        print(f"\n💻 Code à mettre dans Main.cs pour BTC-MACD-ADX:")
        print("-" * 60)
        print("[Parameter(\"adx-window\")]")
        print(f"public int AdxWindowPeriod = {new_params.get('AdxWindowPeriod', 80)};")
        print()
        print("[Parameter(\"adx-lower-percentile\")]")
        print(f"public int AdxLowerPercentile = {new_params.get('AdxLowerPercentile', 5)};")
        print()
        print("[Parameter(\"adx-upper-percentile\")]")
        print(f"public int AdxUpperPercentile = {new_params.get('AdxUpperPercentile', 85)};")
        print("-" * 60)

def main():
    """Main iteration script"""
    print("=" * 80)
    print("SCRIPT D'ITÉRATION - Analyse et Ajustement de Paramètres")
    print("=" * 80)
    print()
    print("Instructions:")
    print("1. Lancer les backtests via QC Web UI")
    print("2. Attendre les résultats (~10-15 min)")
    print("3. Entrer les Sharpe réels ci-dessous")
    print("4. Ce script suggérera des itérations si nécessaires")
    print()

    # Placeholder pour les résultats
    print("Entrez les Sharpe réels (ou appuyez sur Entrée pour utiliser les attendus):")
    print()

    sharpe_btc = input("Sharpe BTC-MACD-ADX (attendu: 0.35): ").strip() or "0.35"
    sharpe_etf = input("Sharpe ETF-Pairs (attendu: 0.5): ").strip() or "0.5"
    sharpe_sector = input("Sharpe Sector-Momentum (attendu: 0.9): ").strip() or "0.9"

    try:
        sharpe_btc = float(sharpe_btc)
        sharpe_etf = float(sharpe_etf)
        sharpe_sector = float(sharpe_sector)
    except:
        print("❌ Entrée invalide. Utilisation des valeurs par défaut.")
        return

    print()
    print("=" * 80)
    print("ANALYSE DES RÉSULTATS")
    print("=" * 80)

    # Analyze each strategy
    for strategy, data in ITERATIONS.items():
        if strategy == 'BTC-MACD-ADX':
            action = analyze_results(sharpe_btc, data['sharpe_attendu'], strategy)
            if action == 'iterate':
                print_alternatives(strategy, data['alternatives'])
        elif strategy == 'ETF-Pairs':
            action = analyze_results(sharpe_etf, data['sharpe_attendu'], strategy)
            if action == 'iterate':
                print_alternatives(strategy, data['alternatives'])
        elif strategy == 'Sector-Momentum':
            action = analyze_results(sharpe_sector, data['sharpe_attendu'], strategy)
            if action == 'iterate':
                print_alternatives(strategy, data['alternatives'])

    print()
    print("=" * 80)
    print("PROCHAINES ÉTAPES")
    print("=" * 80)
    print("1. Si les Sharpe sont bons → Passer en paper trading")
    print("2. Si les Sharpe sont mauvais → Tester les alternatives proposées")
    print("3. Compiler avec: mcp__qc-mcp__create_compile")
    print("4. Relancer backtests avec nouveaux paramètres")
    print("5. Répéter jusqu'à satisfaction")
    print("=" * 80)

if __name__ == "__main__":
    main()
