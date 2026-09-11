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


def generate_synthetic_volume(n_min=390, seed=42):
    """Genere une serie synthetique de volume minute US.

    Parametres
    ----------
    n_min : int
        Nombre de minutes (defaut 390 = 6h30 de trading US).
    seed : int
        Graine RNG pour reproductibilite.

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
    periodicite = 0.25 * np.sin(2 * np.pi * t / 30)

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
        print(f"\nOK : la periodicite injectee a {expected_period:.0f} min "
              f"est detectee en tete (periode observee = {period_top:.1f} min).")
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
