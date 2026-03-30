#!/usr/bin/env python3
"""
Video Helpers - Utilitaires pour les notebooks Video AI
Fonctionnalites : chargement/playback video, extraction frames, assembly, visualisation
"""

import os
import logging
from pathlib import Path
from typing import Optional, Tuple, List, Dict, Any

import numpy as np

logger = logging.getLogger('genai_coursia.video')


# ============================================================================
# Chargement et metadonnees video
# ============================================================================

def get_video_info(path: str) -> Dict[str, Any]:
    """Retourne les metadonnees d'un fichier video.

    Args:
        path: Chemin vers le fichier video

    Returns:
        Dict avec duree, fps, resolution, codec, etc.
    """
    import ffmpeg

    try:
        probe = ffmpeg.probe(str(path))
        video_stream = next(
            (s for s in probe['streams'] if s['codec_type'] == 'video'), None
        )
        audio_stream = next(
            (s for s in probe['streams'] if s['codec_type'] == 'audio'), None
        )

        info = {
            "path": str(path),
            "duration_seconds": float(probe['format'].get('duration', 0)),
            "size_bytes": int(probe['format'].get('size', 0)),
            "format": probe['format'].get('format_name', ''),
        }

        if video_stream:
            # Calcul fps depuis r_frame_rate (ex: "30/1")
            fps_parts = video_stream.get('r_frame_rate', '0/1').split('/')
            fps = int(fps_parts[0]) / int(fps_parts[1]) if len(fps_parts) == 2 else 0

            info.update({
                "width": int(video_stream.get('width', 0)),
                "height": int(video_stream.get('height', 0)),
                "fps": round(fps, 2),
                "video_codec": video_stream.get('codec_name', ''),
                "total_frames": int(video_stream.get('nb_frames', 0)),
            })

        if audio_stream:
            info.update({
                "audio_codec": audio_stream.get('codec_name', ''),
                "audio_sample_rate": int(audio_stream.get('sample_rate', 0)),
                "audio_channels": int(audio_stream.get('channels', 0)),
            })
        else:
            info["has_audio"] = False

        return info

    except Exception as e:
        logger.error(f"Erreur lecture metadonnees video : {e}")
        return {"path": str(path), "error": str(e)}


# ============================================================================
# Extraction de frames
# ============================================================================

def extract_frames(path: str, n_frames: int = 8,
                   output_dir: Optional[str] = None) -> List:
    """Extrait N frames uniformement reparties d'une video.

    Args:
        path: Chemin vers la video
        n_frames: Nombre de frames a extraire
        output_dir: Repertoire de sauvegarde (None = retourne les images PIL)

    Returns:
        Liste d'images PIL.Image
    """
    from PIL import Image
    import decord
    decord.bridge.set_bridge('native')

    vr = decord.VideoReader(str(path))
    total_frames = len(vr)

    if n_frames >= total_frames:
        indices = list(range(total_frames))
    else:
        indices = np.linspace(0, total_frames - 1, n_frames, dtype=int).tolist()

    frames_np = vr.get_batch(indices).asnumpy()
    images = [Image.fromarray(frame) for frame in frames_np]

    if output_dir:
        out_path = Path(output_dir)
        out_path.mkdir(parents=True, exist_ok=True)
        for i, img in enumerate(images):
            img.save(out_path / f"frame_{i:04d}.png")
        logger.info(f"Frames sauvegardees : {out_path} ({len(images)} frames)")

    return images


def extract_frames_at_times(path: str, times_seconds: List[float]) -> List:
    """Extrait des frames a des timestamps specifiques.

    Args:
        path: Chemin vers la video
        times_seconds: Liste de timestamps en secondes

    Returns:
        Liste d'images PIL.Image
    """
    from PIL import Image
    import decord
    decord.bridge.set_bridge('native')

    vr = decord.VideoReader(str(path))
    fps = vr.get_avg_fps()

    indices = [min(int(t * fps), len(vr) - 1) for t in times_seconds]
    frames_np = vr.get_batch(indices).asnumpy()
    return [Image.fromarray(frame) for frame in frames_np]


# ============================================================================
# Visualisation
# ============================================================================

def display_frame_grid(frames: List, cols: int = 4,
                       title: str = "Frames extraites",
                       figsize: Optional[Tuple[int, int]] = None):
    """Affiche une grille de frames dans un notebook.

    Args:
        frames: Liste d'images PIL.Image
        cols: Nombre de colonnes
        title: Titre de la grille
        figsize: Taille de la figure (auto si None)
    """
    import matplotlib.pyplot as plt

    n = len(frames)
    rows = (n + cols - 1) // cols

    if figsize is None:
        figsize = (cols * 3, rows * 3)

    fig, axes = plt.subplots(rows, cols, figsize=figsize)
    if rows == 1:
        axes = [axes] if cols == 1 else axes
    axes_flat = np.array(axes).flatten()

    for i, ax in enumerate(axes_flat):
        if i < n:
            ax.imshow(np.array(frames[i]))
            ax.set_title(f"Frame {i}", fontsize=9)
        ax.axis('off')

    fig.suptitle(title, fontsize=12)
    plt.tight_layout()
    plt.show()


def display_video(path: str, width: int = 640):
    """Affiche une video dans un notebook Jupyter.

    Args:
        path: Chemin vers le fichier video
        width: Largeur d'affichage en pixels
    """
    from IPython.display import Video, display
    display(Video(str(path), embed=True, width=width))


def display_video_comparison(paths: List[str], labels: List[str],
                             n_frames: int = 4):
    """Affiche une comparaison cote a cote de plusieurs videos.

    Args:
        paths: Liste de chemins video
        labels: Liste de labels pour chaque video
        n_frames: Nombre de frames a comparer par video
    """
    import matplotlib.pyplot as plt

    n_videos = len(paths)
    fig, axes = plt.subplots(n_videos, n_frames,
                              figsize=(n_frames * 3, n_videos * 3))

    for i, (path, label) in enumerate(zip(paths, labels)):
        frames = extract_frames(path, n_frames)
        for j, frame in enumerate(frames):
            ax = axes[i, j] if n_videos > 1 else axes[j]
            ax.imshow(np.array(frame))
            if j == 0:
                ax.set_ylabel(label, fontsize=10)
            ax.axis('off')

    plt.tight_layout()
    plt.show()


# ============================================================================
# Assembly video
# ============================================================================

def frames_to_video(frames: List, fps: float, output_path: str,
                    codec: str = "libx264"):
    """Assemble une liste de frames PIL en fichier video.

    Args:
        frames: Liste d'images PIL.Image
        fps: Framerate de la video
        output_path: Chemin du fichier de sortie
        codec: Codec video (libx264, libx265, mpeg4)
    """
    import imageio

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    writer = imageio.get_writer(str(output_path), fps=fps, codec=codec)

    for frame in frames:
        writer.append_data(np.array(frame))

    writer.close()
    logger.info(f"Video assemblee : {output_path} ({len(frames)} frames, {fps}fps)")


def concatenate_videos(paths: List[str], output_path: str):
    """Concatene plusieurs videos en une seule.

    Args:
        paths: Liste de chemins vers les videos source
        output_path: Chemin du fichier de sortie
    """
    from moviepy.editor import VideoFileClip, concatenate_videoclips

    clips = [VideoFileClip(str(p)) for p in paths]
    final = concatenate_videoclips(clips)

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    final.write_videofile(str(output_path), logger=None)

    for clip in clips:
        clip.close()
    final.close()
    logger.info(f"Videos concatenees : {output_path}")


def add_audio_to_video(video_path: str, audio_path: str, output_path: str):
    """Ajoute une piste audio a une video.

    Args:
        video_path: Chemin de la video source
        audio_path: Chemin du fichier audio
        output_path: Chemin du fichier de sortie
    """
    from moviepy.editor import VideoFileClip, AudioFileClip

    video = VideoFileClip(str(video_path))
    audio = AudioFileClip(str(audio_path))

    # Ajuster la duree audio si necessaire
    if audio.duration > video.duration:
        audio = audio.subclip(0, video.duration)

    video_with_audio = video.set_audio(audio)
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    video_with_audio.write_videofile(str(output_path), logger=None)

    video.close()
    audio.close()
    video_with_audio.close()
    logger.info(f"Audio ajoute a la video : {output_path}")


# ============================================================================
# Utilitaires
# ============================================================================

def trim_video(path: str, start: float, end: float, output_path: str):
    """Decoupe un segment de video.

    Args:
        path: Chemin de la video source
        start: Timestamp de debut (secondes)
        end: Timestamp de fin (secondes)
        output_path: Chemin du fichier de sortie
    """
    from moviepy.editor import VideoFileClip

    clip = VideoFileClip(str(path)).subclip(start, end)
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    clip.write_videofile(str(output_path), logger=None)
    clip.close()
    logger.info(f"Video decoupee : {output_path} ({start}s -> {end}s)")


def resize_video(path: str, width: int, height: int, output_path: str):
    """Redimensionne une video.

    Args:
        path: Chemin de la video source
        width: Nouvelle largeur
        height: Nouvelle hauteur
        output_path: Chemin du fichier de sortie
    """
    from moviepy.editor import VideoFileClip

    clip = VideoFileClip(str(path)).resize((width, height))
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    clip.write_videofile(str(output_path), logger=None)
    clip.close()
    logger.info(f"Video redimensionnee : {output_path} ({width}x{height})")
