"""Compile audiobook from FishAudio WAV segments.

Concatenates all fish_seg_*.wav files in order into a single audiobook WAV.
Optionally converts to MP3/FLAC and adds silence between segments.

Usage:
    python compile_audiobook.py [--format wav|mp3|flac] [--silence-ms 300]
"""
import argparse
import struct
import sys
import wave
from pathlib import Path

BASE_DIR = Path(__file__).parent
OUTPUT_DIR = BASE_DIR / "tts_output_fishaudio"


def compile_wav(output_path, wav_files, silence_ms=300):
    """Concatenate WAV files into a single WAV, adding silence between segments."""
    silence_samples = None
    sample_rate = None
    sample_width = None
    n_channels = None

    with wave.open(str(output_path), "wb") as out_wf:
        for i, wav_path in enumerate(wav_files):
            with wave.open(str(wav_path), "rb") as in_wf:
                if i == 0:
                    # Set output params from first file
                    n_channels = in_wf.getnchannels()
                    sample_width = in_wf.getsampwidth()
                    sample_rate = in_wf.getframerate()
                    out_wf.setnchannels(n_channels)
                    out_wf.setsampwidth(sample_width)
                    out_wf.setframerate(sample_rate)
                    silence_samples = int(sample_rate * silence_ms / 1000)
                else:
                    # Add silence between segments
                    silence_bytes = b"\x00" * (silence_samples * sample_width * n_channels)
                    out_wf.writeframes(silence_bytes)

                # Copy audio data
                out_wf.writeframes(in_wf.readframes(in_wf.getnframes()))

            if (i + 1) % 50 == 0:
                print(f"  Processed {i+1}/{len(wav_files)} segments...")

    return output_path


def main():
    parser = argparse.ArgumentParser(description="Compile audiobook from WAV segments")
    parser.add_argument("--format", choices=["wav", "mp3", "flac"], default="wav",
                        help="Output format (wav=lossless, mp3=compressed, flac=lossless compressed)")
    parser.add_argument("--silence-ms", type=int, default=300,
                        help="Silence between segments in milliseconds")
    parser.add_argument("--output", type=str, default=None,
                        help="Output file path (default: auto-generated)")
    args = parser.parse_args()

    # Find all WAV segments, sorted by segment index
    wav_files = sorted(OUTPUT_DIR.glob("fish_seg_*.wav"),
                       key=lambda p: int(p.stem.split("_")[2]))

    if not wav_files:
        print("No WAV segments found in", OUTPUT_DIR)
        sys.exit(1)

    # Check for gaps
    indices = [int(p.stem.split("_")[2]) for p in wav_files]
    expected = list(range(max(indices) + 1))
    missing = set(expected) - set(indices)

    print(f"Found {len(wav_files)} WAV segments (indices 0-{max(indices)})")
    if missing:
        print(f"WARNING: {len(missing)} missing segments: {sorted(missing)[:20]}{'...' if len(missing) > 20 else ''}")

    # Calculate total size
    total_bytes = sum(f.stat().st_size for f in wav_files)
    print(f"Total input size: {total_bytes / 1024 / 1024:.1f} MB")

    # Output path
    output_name = args.output or f"boule_de_suif_audiobook.{args.format}"
    output_path = OUTPUT_DIR / output_name

    print(f"\nCompiling audiobook to {output_path}...")
    print(f"Silence between segments: {args.silence_ms}ms")

    # Always compile to WAV first
    wav_path = output_path if args.format == "wav" else OUTPUT_DIR / "boule_de_suif_audiobook.wav"
    compile_wav(wav_path, wav_files, args.silence_ms)

    # Get duration
    with wave.open(str(wav_path), "rb") as wf:
        duration = wf.getnframes() / wf.getframerate()

    print(f"\nAudiobook compiled!")
    print(f"  Duration: {duration:.0f}s ({duration/60:.1f}min)")
    print(f"  Size: {wav_path.stat().st_size / 1024 / 1024:.1f} MB")
    print(f"  Segments: {len(wav_files)}")
    print(f"  File: {wav_path}")

    # Convert to MP3/FLAC if requested
    if args.format != "wav":
        print(f"\nConverting to {args.format.upper()}...")
        import subprocess
        ffmpeg_cmd = ["ffmpeg", "-y", "-i", str(wav_path)]
        if args.format == "mp3":
            ffmpeg_cmd += ["-codec:a", "libmp3lame", "-qscale:a", "2", str(output_path)]
        elif args.format == "flac":
            ffmpeg_cmd += ["-codec:a", "flac", "-compression_level", "8", str(output_path)]

        result = subprocess.run(ffmpeg_cmd, capture_output=True, text=True)
        if result.returncode == 0:
            print(f"  Converted: {output_path} ({output_path.stat().st_size / 1024 / 1024:.1f} MB)")
            # Remove intermediate WAV
            if wav_path != output_path:
                wav_path.unlink()
                print(f"  Removed intermediate WAV")
        else:
            print(f"  Conversion failed: {result.stderr[:200]}")
            print(f"  WAV kept at: {wav_path}")


if __name__ == "__main__":
    main()
