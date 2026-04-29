"""
GPU Training Utilities pour QuantConnect / PyTorch

Utilitaires pour l'entrainement GPU securise sur machines avec contraintes thermiques.
Concu pour le MSI GE76 RTX 3080 Ti Laptop (3 crashes GPU constates en avril 2026).

Fonctions principales:
    - get_gpu_temp: Lecture temperature GPU via nvidia-smi
    - thermal_check: Verifie et pause si temperature trop elevee (inter-epoch)
    - batch_thermal_check: Verifie temperature tous les N batches (intra-epoch)
    - setup_amp: Configure AMP (Mixed Precision) pour reduire VRAM/chauffe
    - checkpoint_save: Sauvegarde un checkpoint complet (repreneable)
    - checkpoint_resume: Reprend depuis un checkpoint ou modele final
    - TrainingCheckpoint: Classe utilitaire pour gerer le cycle checkpoint/save

Usage dans un notebook:
    from shared.gpu_training import TrainingCheckpoint

    ckpt = TrainingCheckpoint(
        checkpoint_path='model_checkpoint.pt',
        model_save_path='final_model.pt',
        max_temp=87, cool_sleep=15
    )
    start_epoch, history = ckpt.resume(model, optimizer, scheduler, grad_scaler)

    for epoch in range(start_epoch, EPOCHS):
        ckpt.thermal_check()
        train_metrics = train_epoch(model, ...)
        val_metrics = evaluate(model, ...)
        ckpt.update(epoch, val_metrics['loss'], history, model, optimizer, scheduler, grad_scaler)

    ckpt.finalize(model)

Architecture:
    - AMP (Mixed Precision): torch.amp.autocast + GradScaler
    - Thermal watchdog: nvidia-smi via subprocess, seuil configurable
    - Checkpoint 3 cas: modele final -> skip, checkpoint -> resume, rien -> start
"""

import os
import time
import subprocess
import copy
from typing import Dict, Any, Optional, Tuple

import torch
import torch.nn as nn


def get_gpu_temp() -> int:
    """
    Lit la temperature GPU via nvidia-smi.

    Returns
    -------
    int
        Temperature en Celsius, 0 si erreur ou pas de GPU.
    """
    try:
        result = subprocess.run(
            ['nvidia-smi', '--query-gpu=temperature.gpu',
             '--format=csv,noheader,nounits'],
            capture_output=True, text=True, timeout=5
        )
        return int(result.stdout.strip())
    except Exception:
        return 0


def thermal_check(max_temp: int = 80, cool_sleep: int = 15, verbose: bool = True) -> int:
    """
    Verifie la temperature GPU et pause si necessaire.

    Parameters
    ----------
    max_temp : int
        Seuil en Celsius au-dela duquel on pause (defaut: 87).
    cool_sleep : int
        Duree de pause en secondes si seuil depasse (defaut: 15).
    verbose : bool
        Afficher le message de pause (defaut: True).

    Returns
    -------
    int
        Temperature actuelle en Celsius.
    """
    if not torch.cuda.is_available():
        return 0

    temp = get_gpu_temp()
    if temp > max_temp:
        if verbose:
            print(f"  [THERMAL] GPU {temp}C > {max_temp}C, pause {cool_sleep}s...")
        time.sleep(cool_sleep)
    return temp


def batch_thermal_check(
    batch_idx: int,
    check_every: int = 10,
    max_temp: int = 80,
    cool_sleep: int = 15,
    verbose: bool = True
) -> int:
    """
    Intra-epoch thermal check: called every N batches inside train_epoch().

    Prevents GPU thermal crashes by checking temperature mid-epoch instead
    of only between epochs. On MSI GE76 RTX 3080 Ti, temperature can spike
    from ~80C to >96C during a single epoch (20-40s sustained load).

    Parameters
    ----------
    batch_idx : int
        Current batch index (0-based).
    check_every : int
        Check temperature every N batches (defaut: 10).
        nvidia-smi call takes ~5ms, so overhead is negligible.
    max_temp : int
        Seuil en Celsius au-dela duquel on pause (defaut: 80).
    cool_sleep : int
        Duree de pause en secondes si seuil depasse (defaut: 15).
    verbose : bool
        Afficher le message de pause (defaut: True).

    Returns
    -------
    int
        Temperature actuelle en Celsius, 0 si check skipped ou pas de GPU.
    """
    if batch_idx % check_every != 0:
        return 0
    return thermal_check(max_temp, cool_sleep, verbose)


def setup_amp() -> Tuple[bool, torch.amp.GradScaler]:
    """
    Configure AMP (Mixed Precision) pour reduire VRAM et chaleur GPU.

    Returns
    -------
    tuple (use_amp, grad_scaler)
        use_amp : bool - True si AMP est actif (GPU disponible)
        grad_scaler : torch.amp.GradScaler - Scaler pour le gradient scaling
    """
    use_amp = torch.cuda.is_available()
    grad_scaler = torch.amp.GradScaler('cuda', enabled=use_amp)
    return use_amp, grad_scaler


def amp_train_step(
    model: nn.Module,
    x_batch: torch.Tensor,
    y_batch: torch.Tensor,
    optimizer: torch.optim.Optimizer,
    loss_fn,
    grad_scaler: Optional[torch.amp.GradScaler] = None,
    max_norm: float = 1.0
) -> torch.Tensor:
    """
    Execute une etape de training avec AMP.

    Parameters
    ----------
    model : nn.Module
        Le modele PyTorch.
    x_batch : Tensor
        Batch d'entrees.
    y_batch : Tensor
        Batch de cibles.
    optimizer : Optimizer
        L'optimiseur.
    loss_fn : callable
        Fonction de loss (model output, target) -> loss.
    grad_scaler : GradScaler or None
        Si fourni, utilise AMP.
    max_norm : float
        Norme max pour le gradient clipping (defaut: 1.0).

    Returns
    -------
    Tensor
        La loss (detached).
    """
    use_amp = grad_scaler is not None and grad_scaler.is_enabled()
    optimizer.zero_grad()

    with torch.amp.autocast('cuda', enabled=use_amp):
        output = model(x_batch)
        loss = loss_fn(output, y_batch)

    if use_amp:
        grad_scaler.scale(loss).backward()
        grad_scaler.unscale_(optimizer)
        torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=max_norm)
        grad_scaler.step(optimizer)
        grad_scaler.update()
    else:
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=max_norm)
        optimizer.step()

    return loss.detach()


def checkpoint_save(
    path: str,
    epoch: int,
    model: nn.Module,
    optimizer: torch.optim.Optimizer,
    scheduler=None,
    grad_scaler: Optional[torch.amp.GradScaler] = None,
    best_val_loss: float = float('inf'),
    history: Optional[Dict] = None,
    extra: Optional[Dict] = None
) -> None:
    """
    Sauvegarde un checkpoint complet pour reprise apres crash.

    Parameters
    ----------
    path : str
        Chemin du fichier checkpoint.
    epoch : int
        Numero d'epoch (1-based, apres completion).
    model : nn.Module
        Modele PyTorch.
    optimizer : Optimizer
        Optimiseur.
    scheduler : optional
        LR Scheduler.
    grad_scaler : GradScaler, optional
        AMP GradScaler.
    best_val_loss : float
        Meilleure val loss observee.
    history : dict, optional
        Historique d'entrainement.
    extra : dict, optional
        Donnees supplementaires a sauvegarder.
    """
    state = {
        'epoch': epoch,
        'model_state_dict': model.state_dict(),
        'optimizer_state_dict': optimizer.state_dict(),
        'best_val_loss': best_val_loss,
        'history': history or {},
    }
    if scheduler is not None:
        state['scheduler_state_dict'] = scheduler.state_dict()
    if grad_scaler is not None:
        state['grad_scaler_state'] = grad_scaler.state_dict()
    if extra is not None:
        state['extra'] = extra

    torch.save(state, path)


def checkpoint_resume(
    checkpoint_path: str,
    model_save_path: str,
    model: nn.Module,
    optimizer: Optional[torch.optim.Optimizer] = None,
    scheduler=None,
    grad_scaler: Optional[torch.amp.GradScaler] = None,
    device: Optional[torch.device] = None
) -> Tuple[int, float, Dict, Optional[Dict]]:
    """
    Reprise depuis checkpoint ou modele final (3 cas).

    Cas 1: model_save_path existe -> charge et retourne (EPOCHS, loss, history, extra)
    Cas 2: checkpoint_path existe -> resume optim/scheduler/scaler
    Cas 3: rien -> retourne (0, inf, {}, None)

    Parameters
    ----------
    checkpoint_path : str
        Chemin du checkpoint complet.
    model_save_path : str
        Chemin du modele final (state_dict only).
    model : nn.Module
        Modele PyTorch a charger.
    optimizer : Optimizer, optional
        Optimiseur a restaurer.
    scheduler : optional
        LR Scheduler a restaurer.
    grad_scaler : GradScaler, optional
        AMP GradScaler a restaurer.
    device : torch.device, optional
        Device pour le chargement.

    Returns
    -------
    tuple (start_epoch, best_val_loss, history, extra)
        start_epoch : int - Epoch de depart (0 si from scratch, EPOCHS si modele final)
        best_val_loss : float - Meilleure val loss observee
        history : dict - Historique d'entrainement
        extra : dict or None - Donnees supplementaires
    """
    map_loc = device or ('cuda' if torch.cuda.is_available() else 'cpu')
    empty_history = {}

    if os.path.exists(model_save_path):
        print(f"Modele final trouve: {model_save_path}")
        save_dict = torch.load(model_save_path, weights_only=False, map_location=map_loc)
        model.load_state_dict(save_dict['model_state_dict'])
        print("Modele charge, entrainement saute.")
        extra = save_dict.get('extra', save_dict)
        return -1, float('inf'), empty_history, extra

    elif os.path.exists(checkpoint_path):
        print(f"Checkpoint trouve: {checkpoint_path}")
        ckpt = torch.load(checkpoint_path, weights_only=False, map_location=map_loc)
        model.load_state_dict(ckpt['model_state_dict'])

        if optimizer is not None:
            optimizer.load_state_dict(ckpt['optimizer_state_dict'])
        if scheduler is not None and 'scheduler_state_dict' in ckpt:
            scheduler.load_state_dict(ckpt['scheduler_state_dict'])
        if grad_scaler is not None and 'grad_scaler_state' in ckpt:
            grad_scaler.load_state_dict(ckpt['grad_scaler_state'])

        start_epoch = ckpt['epoch']
        best_val_loss = ckpt.get('best_val_loss', float('inf'))
        history = ckpt.get('history', empty_history)
        extra = ckpt.get('extra', None)

        print(f"Resume a l'epoch {start_epoch}, best_val_loss={best_val_loss:.4f}")
        return start_epoch, best_val_loss, history, extra

    else:
        print("Aucun checkpoint ni modele final. Demarrage from scratch.")
        return 0, float('inf'), empty_history, None


class TrainingCheckpoint:
    """
    Utilitaire de gestion du cycle checkpoint/save pour un entrainement GPU.

    Gere le thermal watchdog, la sauvegarde/chargement de checkpoints,
    et la sauvegarde du modele final.

    Example
    -------
    >>> from shared.gpu_training import TrainingCheckpoint
    >>> ckpt = TrainingCheckpoint('model_checkpoint.pt', 'final_model.pt')
    >>> start_epoch, history = ckpt.resume(model, optimizer, scheduler, grad_scaler)
    >>> for epoch in range(start_epoch, EPOCHS):
    ...     ckpt.thermal_check()
    ...     train_metrics = train_epoch(model, ..., thermal_fn=ckpt.batch_thermal_check)
    ...     val_metrics = evaluate(model, ...)
    ...     ckpt.update(epoch, val_metrics['loss'], history, model, optimizer, scheduler, grad_scaler)
    >>> ckpt.finalize(model)
    """

    def __init__(
        self,
        checkpoint_path: str = 'model_checkpoint.pt',
        model_save_path: str = 'final_model.pt',
        max_temp: int = 80,
        cool_sleep: int = 15,
        patience: int = 7,
        thermal_check_every: int = 10,
    ):
        """
        Parameters
        ----------
        checkpoint_path : str
            Chemin du checkpoint complet (resumable, NE PAS commit).
        model_save_path : str
            Chemin du modele final (state_dict only, OK pour commit).
        max_temp : int
            Seuil thermique en Celsius (defaut: 80).
        cool_sleep : int
            Pause en secondes si seuil depasse (defaut: 15).
        patience : int
            Patience pour early stopping (defaut: 7).
        thermal_check_every : int
            Check temperature every N batches intra-epoch (defaut: 10).
        """
        self.checkpoint_path = checkpoint_path
        self.model_save_path = model_save_path
        self.max_temp = max_temp
        self.cool_sleep = cool_sleep
        self.patience = patience
        self.thermal_check_every = thermal_check_every

        self.best_val_loss = float('inf')
        self.patience_counter = 0
        self.best_model_state = None

    def resume(
        self,
        model: nn.Module,
        optimizer: Optional[torch.optim.Optimizer] = None,
        scheduler=None,
        grad_scaler: Optional[torch.amp.GradScaler] = None,
        device: Optional[torch.device] = None,
        default_history: Optional[Dict] = None
    ) -> Tuple[int, Dict]:
        """
        Tente de reprendre depuis un checkpoint ou modele final.

        Returns
        -------
        tuple (start_epoch, history)
            start_epoch : -1 si modele final (skip training), 0+ sinon
            history : dict de listes de metriques
        """
        start_epoch, best_val_loss, history, _ = checkpoint_resume(
            self.checkpoint_path,
            self.model_save_path,
            model, optimizer, scheduler, grad_scaler, device
        )
        self.best_val_loss = best_val_loss

        if default_history and not history:
            history = default_history

        return start_epoch, history

    def thermal_check(self) -> int:
        """Verifie la temperature GPU et pause si necessaire (inter-epoch)."""
        return thermal_check(self.max_temp, self.cool_sleep)

    def batch_thermal_check(self, batch_idx: int) -> int:
        """Verifie la temperature GPU intra-epoch (tous les N batches)."""
        return batch_thermal_check(
            batch_idx, self.thermal_check_every,
            self.max_temp, self.cool_sleep
        )

    def update(
        self,
        epoch: int,
        val_loss: float,
        history: Dict,
        model: nn.Module,
        optimizer: torch.optim.Optimizer,
        scheduler=None,
        grad_scaler: Optional[torch.amp.GradScaler] = None,
        extra: Optional[Dict] = None
    ) -> bool:
        """
        Met a jour le checkpoint si val_loss s'est ameliore.
        Retourne True si c'est un nouveau best, False sinon.
        Gere aussi le compteur de patience.

        Parameters
        ----------
        epoch : int
            Numero d'epoch (0-based).
        val_loss : float
            Validation loss de cette epoch.
        history : dict
            Historique d'entrainement.
        model : nn.Module
            Modele PyTorch.
        optimizer : Optimizer
            Optimiseur.
        scheduler : optional
            LR Scheduler.
        grad_scaler : GradScaler, optional
            AMP GradScaler.
        extra : dict, optional
            Donnees supplementaires.

        Returns
        -------
        bool
            True si nouveau best modele, False sinon.
        """
        if val_loss < self.best_val_loss:
            self.best_val_loss = val_loss
            self.patience_counter = 0
            self.best_model_state = {k: v.cpu().clone() for k, v in model.state_dict().items()}

            checkpoint_save(
                self.checkpoint_path,
                epoch + 1,
                model, optimizer, scheduler, grad_scaler,
                self.best_val_loss, history, extra
            )
            return True
        else:
            self.patience_counter += 1
            return False

    def should_stop(self) -> bool:
        """Retourne True si la patience est epuisee."""
        return self.patience_counter >= self.patience

    def finalize(self, model: nn.Module, extra: Optional[Dict] = None) -> None:
        """
        Charge le meilleur modele et sauvegarde le modele final.

        Parameters
        ----------
        model : nn.Module
            Modele PyTorch.
        extra : dict, optional
            Donnees supplementaires a inclure (scaler, config, etc.).
        """
        if self.best_model_state is not None:
            model.load_state_dict(self.best_model_state)

        save_dict = {'model_state_dict': model.state_dict()}
        if extra:
            save_dict.update(extra)

        torch.save(save_dict, self.model_save_path)
        print(f"Modele final sauvegarde: {self.model_save_path}")
