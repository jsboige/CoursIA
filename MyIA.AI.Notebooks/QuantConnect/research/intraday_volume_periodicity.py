"""
intraday_volume_periodicity.py - Companion script pedagogique

Illustration du concept de periodicite intraday du volume boursier,
d'apres Wu, L., Zhang, R. & Dai, Y. (2025), *Spectral Volume Models:
Universal High-Frequency Periodicities in Intraday Trading Activities*,
Management Science, doi:10.1287/mnsc.2024.06215 (nov. 2025 ;
preprint SSRN 4230610).

Ce script reproduit la logique du notebook
intraday_volume_periodicity.ipynb sous forme d'un script lineaire
executable en CLI (utile pour batch / CI / debug) :

1. Genere une serie synthetique de volume minute US (390 minutes) :
   - Fenetre U-shape (pic ouverture + pic close, creux mid-day)
   - Periodicite artificielle a 30 min (fond de panier mid-day)
   - Bruit log-normal multiplicatif (seed=42 pour reproductibilite)
2. Calcule le spectre de puissance (FFT) et detecte les frequences
   dominantes par top-N (ici 5).
3. Confirme la detection de la periodicite injectee (periode 30 min).
4. Mesure un controle negatif : compare, sur 20 seeds, le bras temoin
   (sans periodicite) au bras periodique, puis balaie l'amplitude
   injectee pour situer le seuil de detection. Chercher la periode
   injectee ne prouve rien en soi ; c'est l'ecart entre les deux bras
   qui mesure la capacite du detecteur.

Le script expose les memes primitives que le notebook pour que les
exercices puissent les appeler directement (sans re-implementation) :

- generate_synthetic_volume(seed) : serie 1D numpy, axe t = minutes.
- detect_periods(volume, top_n) : top-N (frequence, periode, puissance).
- apply_hann_window(volume) : signal fenetre (centre * Hann).
- aggregate_spectra(seed_list, n_days) : spectre moyen sur N jours.

Usage :
    python intraday_volume_periodicity.py

Sortie : stdout (texte plain), 0 si succes.

Dependances : numpy >= 1.25 (helper scalaire/vecteur compatible).
"""

import numpy as np


def generate_synthetic_volume(n_min=390, seed=42, inject=True, amplitude=0.25):
    """Genere une serie synthetique de volume minute US.

    Parametres
    ----------
    n_min : int
        Nombre de minutes (defaut 390 = 6h30 de trading US).
    seed : int
        Graine RNG pour reproductibilite.
    inject : bool
        Si False, la serie ne contient AUCUNE periodicite : c'est le bras
        temoin du controle negatif (U-shape + bruit seulement).
    amplitude : float
        Amplitude de la sinusoide 30 min (ignoree si inject=False).

    Retour
    ------
    t : np.ndarray shape (n_min,)
        Axe temporel en minutes depuis l'ouverture.
    volume : np.ndarray shape (n_min,)
        Volume synthetique (unites arbitraires).
    """
    rng = np.random.default_rng(seed=seed)
    t = np.arange(n_min)

    # Fenetre U-shape : 3 gaussiennes centrees sur open / close / mid
    u_shape = (
        1.0 + 1.2 * np.exp(-((t - 30) ** 2) / (2 * 25 ** 2))
        + 0.9 * np.exp(-((t - 380) ** 2) / (2 * 30 ** 2))
        + 0.3 * np.exp(-((t - 200) ** 2) / (2 * 60 ** 2))
    )

    # Periodicite artificielle : 30 min (Wu et al. trouvent typiquement
    # un cycle de l'ordre de 30 min sur des donnees reelles).
    periodicite = amplitude * np.sin(2 * np.pi * t / 30) if inject else 0.0

    # Bruit log-normal multiplicatif (heteroscedasticite typique du volume).
    bruit = rng.lognormal(mean=0.0, sigma=0.6, size=n_min)

    volume = u_shape * (1.0 + periodicite) * bruit
    return t, volume


def detect_periods(volume, top_n=5):
    """Detecte les top-N periodicites par FFT.

    Parametres
    ----------
    volume : np.ndarray
        Serie temporelle (espacement uniforme 1 minute).
    top_n : int
        Nombre de pics a retourner.

    Retour
    ------
    list[tuple[float, float, float]]
        Liste (frequence_cycle_par_min, periode_min, puissance), triee
        par puissance decroissante.
    """
    n = len(volume)
    spectrum = np.abs(np.fft.rfft(volume - volume.mean())) ** 2
    freqs = np.fft.rfftfreq(n, d=1.0)  # cycles/min, espacement 1 min

    # Spectre symmetrique : on prend les N indices les plus energetiques
    # en excluant f=0 (DC).
    spectrum_no_dc = spectrum.copy()
    spectrum_no_dc[0] = 0
    top_idx = np.argsort(spectrum_no_dc)[::-1][:top_n]

    results = []
    for idx in top_idx:
        f = float(freqs[idx])
        if f == 0:
            continue
        period = 1.0 / f
        power = float(spectrum[idx])
        results.append((f, period, power))
    return results


def apply_hann_window(volume):
    """Applique une fenetre de Hann au signal centre.

    Parametre
    ---------
    volume : np.ndarray
        Serie temporelle brute (pas forcement centree).

    Retour
    ------
    np.ndarray
        Signal centre * Hann, pret pour FFT.
    """
    n = len(volume)
    window = np.hanning(n)
    return (volume - volume.mean()) * window


def aggregate_spectra(seed_list):
    """Calcule le spectre moyen sur une liste de seeds (journees).

    Parametre
    ---------
    seed_list : list[int]
        Liste de seeds, un par journee.

    Retour
    ------
    np.ndarray
        Spectre moyen (meme taille que celui d'un jour individuel).
    """
    spectra = []
    for seed in seed_list:
        _, vol = generate_synthetic_volume(seed=seed)
        s = np.abs(np.fft.rfft(vol - vol.mean())) ** 2
        spectra.append(s)
    return np.mean(np.array(spectra), axis=0)


DEFAULT_SEEDS = [0, 1, 7, 42, 99, 2, 3, 5, 11, 13,
                 17, 23, 29, 31, 37, 41, 43, 47, 53, 61]


def rank_and_ratio(volume):
    """Rang du bac a 30 min et rapport de puissance a la mediane du spectre.

    Parametre
    ---------
    volume : np.ndarray
        Serie temporelle (espacement uniforme 1 minute).

    Retour
    ------
    (int, float)
        Rang du bac 30 min (1 = pic dominant, continu DC exclu) et
        rapport puissance(bac 30 min) / mediane(spectre hors DC).
    """
    n = len(volume)
    spectrum = np.abs(np.fft.rfft(volume - volume.mean())) ** 2
    spectrum = spectrum.copy()
    spectrum[0] = 0.0                       # on ecarte le continu (DC)
    freqs = np.fft.rfftfreq(n, d=1.0)
    i30 = int(np.argmin(np.abs(freqs - 1.0 / 30.0)))
    order = np.argsort(spectrum)[::-1]
    rank = int(np.where(order == i30)[0][0]) + 1
    return rank, float(spectrum[i30] / np.median(spectrum[1:]))


def _arm_stats(seeds, inject, amplitude=0.25):
    """Statistiques d'un bras : pics dominants, rangs et rapports."""
    ranks, ratios = [], []
    for seed in seeds:
        _, vol = generate_synthetic_volume(seed=seed, inject=inject,
                                           amplitude=amplitude)
        rank, ratio = rank_and_ratio(vol)
        ranks.append(rank)
        ratios.append(ratio)
    return {
        "pic_dominant": sum(1 for r in ranks if r == 1),
        "rang_median": float(np.median(ranks)),
        "rapport_median": float(np.median(ratios)),
        "rapport_min": min(ratios),
        "rapport_max": max(ratios),
        "ratios": ratios,
    }


def null_control(seeds=None, amplitude=0.25):
    """Controle negatif : bras temoin (sans periodicite) contre bras periodique.

    Chercher une periode qu'on a soi-meme injectee ne mesure rien : le
    resultat est garanti. La mesure utile est l'ecart entre le bras temoin
    et le bras periodique, sur les memes seeds.

    Parametres
    ----------
    seeds : list[int] | None
        Seeds des deux bras (defaut : 20 seeds).
    amplitude : float
        Amplitude de la sinusoide dans le bras periodique.

    Retour
    ------
    (dict, dict)
        (stats_temoin, stats_periodique) au format de _arm_stats.
    """
    if seeds is None:
        seeds = DEFAULT_SEEDS
    return _arm_stats(seeds, inject=False, amplitude=amplitude), \
        _arm_stats(seeds, inject=True, amplitude=amplitude)


def main():
    t, volume = generate_synthetic_volume()
    print(
        f"Serie synthetique generee : n={len(t)} minutes, "
        f"pic={volume.max():.1f}, creux={volume.min():.1f}, "
        f"SNR periodicite/bruit ~0.25/{np.std(volume / volume.mean()):.2f}"
    )

    top = detect_periods(volume, top_n=5)
    print(f"\nTop {len(top)} frequences detectees :")
    for f, period, power in top:
        print(f"  f = {f:.4f} cycle/min  ->  periode {period:.1f} min  "
              f"(puissance {power:.0f})")

    # Verification : la periodicite 30 min injectee doit apparaitre en tete.
    f_top, period_top, _ = top[0]
    expected_period = 30.0
    period_match = abs(period_top - expected_period) < 1.0
    if period_match:
        print(f"\nOK (seed 42) : la periodicite injectee a {expected_period:.0f} min "
              f"est detectee en tete (periode observee = {period_top:.1f} min). "
              f"Une seed favorable ne dit rien de la robustesse -- c'est ce que "
              f"mesure le controle negatif ci-dessous.")
    else:
        print(f"\nWARN : la periodicite {expected_period:.0f} min injectee "
              f"n'est pas en tete (periode tete = {period_top:.1f} min).")

    # Demonstration : aggregation multi-jours (5 seeds), exercice 3 du notebook.
    spectrum_mean = aggregate_spectra([0, 1, 7, 42, 99])
    idx_top_mean = np.argsort(spectrum_mean)[::-1][:5]
    n = len(volume)
    freqs = np.fft.rfftfreq(n, d=1.0)
    print("\nTop 5 sur spectre moyen (5 jours, exercice 3 du notebook) :")
    for i in idx_top_mean:
        f = float(freqs[i])
        period_min = 1.0 / f if f > 0 else float('inf')
        print(f"  f = {f:.4f} cycle/min  ->  periode {period_min:.1f} min  "
              f"(puissance {spectrum_mean[i]:.0f})")

    # Controle negatif : chercher la periode injectee ne prouve rien seul.
    temoin, periodique = null_control()
    n_seeds = len(DEFAULT_SEEDS)
    print(f"\nControle negatif ({n_seeds} seeds par bras, amplitude 0.25) :")
    print(f"{'bras':<11} {'pic dominant':>13} {'rang median':>12} "
          f"{'rapport median':>15} {'rapport min':>12} {'rapport max':>12}")
    for nom, stats in (("temoin", temoin), ("periodique", periodique)):
        print(f"{nom:<11} {stats['pic_dominant']:>6}/{n_seeds:<6} "
              f"{stats['rang_median']:>12.0f} {stats['rapport_median']:>15.1f} "
              f"{stats['rapport_min']:>12.2f} {stats['rapport_max']:>12.2f}")
    inversions = sum(1 for a in temoin["ratios"] for b in periodique["ratios"]
                     if a >= b)
    paires = len(temoin["ratios"]) * len(periodique["ratios"])
    print(f"Paires (temoin, periodique) ou le temoin fait aussi bien ou mieux : "
          f"{inversions} / {paires}")

    # Seuil de detection : balayage de l'amplitude injectee.
    print("\nSeuil de detection :")
    print(f"{'amplitude':>10} {'bac 30 min en tete':>20} {'rang median':>12} "
          f"{'rapport median':>15}")
    for amp in (0.00, 0.02, 0.05, 0.10, 0.15, 0.25, 0.50):
        stats = _arm_stats(DEFAULT_SEEDS, inject=(amp > 0.0), amplitude=amp)
        print(f"{amp:>10.2f} {stats['pic_dominant']:>14}/{n_seeds:<5} "
              f"{stats['rang_median']:>12.0f} {stats['rapport_median']:>15.1f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
