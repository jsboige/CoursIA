"""Analyze MoE+regimes results for issue #754 verdict."""
import json, glob, os
from collections import defaultdict
import numpy as np

def load_results(results_dir):
    files = sorted(glob.glob(os.path.join(results_dir, 'moe_regimes_*_seed*.json')))
    groups = defaultdict(list)
    for f in files:
        basename = os.path.basename(f).replace('.json', '')
        parts = basename.split('_')
        # moe_regimes_BTC-USD_lstm_hmm_seed0
        symbol = parts[2]
        expert = parts[3]
        method = parts[4]
        seed = int(parts[5].replace('seed', ''))
        with open(f) as fp:
            data = json.load(fp)
        groups[f'{symbol}_{method}'].append({
            'seed': seed,
            'diracc': data['moe_mean_diracc'],
            'std': data['moe_std_diracc'],
            'fold_diraccs': data['moe_fold_diraccs'],
            'baseline': data['majority_baseline_acc'],
            'beats': data['beats_majority'],
            'regimes': data['regime_counts'],
            'n_folds': data['n_folds'],
            'n_samples': data['n_samples'],
        })
    return groups

def verdict(groups):
    print('=' * 70)
    print('MoE+Regimes #754 Verdict Report')
    print('=' * 70)
    
    results_table = []
    
    for key in sorted(groups.keys()):
        entries = sorted(groups[key], key=lambda x: x['seed'])
        symbol, method = key.split('_')
        baseline = entries[0]['baseline']
        seeds = [e['seed'] for e in entries]
        diraccs = [e['diracc'] for e in entries]
        mean_da = np.mean(diraccs)
        std_da = np.std(diraccs)
        delta = mean_da - baseline
        delta_pp = delta * 100
        
        # Statistical test (scipy if available, else manual)
        n_seeds = len(diraccs)
        if n_seeds >= 2:
            se = std_da / np.sqrt(n_seeds)
            t_stat = delta / se if se > 0 else 0
            # p-value approximation
            from scipy import stats as sp_stats
            _, p_val = sp_stats.ttest_1samp(diraccs, baseline)
        else:
            t_stat = 0
            p_val = 1.0
            se = 0
        
        # Verdict logic
        edge_2std = 2 * std_da
        if mean_da > baseline and p_val < 0.05 and delta > edge_2std:
            verdict_str = 'BEATS'
        elif mean_da < baseline and p_val < 0.05:
            verdict_str = 'NO BEATS'
        elif n_seeds < 4:
            verdict_str = 'INCONCLUSIVE (<' + str(4) + ' seeds)'
        else:
            verdict_str = 'INCONCLUSIVE'
        
        # Transaction costs: 10bps crypto round-trip per trade
        # Conservative: if edge < 10bps (0.1%), not profitable after costs
        tx_cost_bps = 10
        edge_bps = delta_pp * 100  # convert pp to bps
        
        print(f'\n--- {symbol} ({method}) ---')
        print(f'  Seeds: {seeds}')
        print(f'  Baseline: {baseline:.4f}')
        print(f'  MoE DirAcc: {mean_da:.4f} +/- {std_da:.4f} (n={n_seeds})')
        print(f'  Delta: {delta_pp:+.2f}pp ({edge_bps:+.0f} bps)')
        print(f'  2*std: {2*std_da:.4f} ({2*std_da*10000:.0f} bps)')
        print(f'  t-stat: {t_stat:.3f}, p-value: {p_val:.4f}')
        print(f'  Tx costs: {tx_cost_bps} bps (crypto round-trip)')
        print(f'  Profitable after tx costs: {"YES" if edge_bps > tx_cost_bps else "NO"}')
        print(f'  VERDICT: {verdict_str}')
        
        results_table.append({
            'coin': symbol, 'method': method, 'seeds': n_seeds,
            'mean_diracc': mean_da, 'std_diracc': std_da,
            'baseline': baseline, 'delta_pp': delta_pp,
            'p_value': p_val, 'verdict': verdict_str,
            'profitable_after_tx': edge_bps > tx_cost_bps
        })
    
    print('\n' + '=' * 70)
    print('SUMMARY TABLE')
    print('=' * 70)
    print(f'{"Coin":<10} {"Method":<8} {"Seeds":<6} {"DirAcc":<8} {"Baseline":<9} {"Delta":<8} {"p-val":<8} {"Verdict"}')
    print('-' * 70)
    for r in results_table:
        print(f'{r["coin"]:<10} {r["method"]:<8} {r["seeds"]:<6} {r["mean_diracc"]:.4f}  {r["baseline"]:.4f}   {r["delta_pp"]:+.2f}pp {r["p_value"]:.4f}  {r["verdict"]}')
    
    # Overall verdict
    beats = sum(1 for r in results_table if r['verdict'] == 'BEATS')
    no_beats = sum(1 for r in results_table if 'NO BEATS' in r['verdict'])
    inconclusive = len(results_table) - beats - no_beats
    print(f'\nOverall: {beats} BEATS, {no_beats} NO BEATS, {inconclusive} INCONCLUSIVE out of {len(results_table)} experiments')
    
    return results_table

if __name__ == '__main__':
    import sys
    results_dir = sys.argv[1] if len(sys.argv) > 1 else 'results/moe_regimes_754'
    groups = load_results(results_dir)
    results = verdict(groups)
