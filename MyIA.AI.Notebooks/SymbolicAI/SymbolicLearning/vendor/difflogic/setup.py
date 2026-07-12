from setuptools import setup
from torch.utils.cpp_extension import BuildExtension
import os
import subprocess

# SL-12 fork: build CUDA extension only when (a) CUDA runtime is available AND
# (b) the system CUDA Toolkit version matches the version PyTorch was compiled
# against. Without these guards, `pip install difflogic` fails on machines where
# CUDA Toolkit version differs from torch.version.cuda (e.g. CUDA 13.3 system
# vs torch 2.7.0+cu118). Upstream bug: setup.py unconditionally includes
# CUDAExtension even when the install environment is CPU-only or has a
# mismatched CUDA Toolkit.

def _detect_nvcc_version():
    """Return major version of system CUDA Toolkit (via nvcc), or None if missing."""
    nvcc = os.environ.get('CUDA_HOME', '') and os.path.join(os.environ['CUDA_HOME'], 'bin', 'nvcc')
    if not nvcc or not os.path.isfile(nvcc):
        # Fallback: try nvcc on PATH.
        nvcc = 'nvcc'
    try:
        out = subprocess.check_output([nvcc, '--version'], stderr=subprocess.STDOUT, text=True, timeout=10)
    except Exception:
        return None
    # Output line: "Cuda compilation tools, release 13.3, V13.3.107"
    for line in out.splitlines():
        if 'release' in line.lower():
            parts = line.split('release')
            if len(parts) >= 2:
                ver = parts[1].strip().split(',')[0].strip()
                try:
                    return ver.split('.')[0]
                except Exception:
                    return None
    return None


try:
    import torch
    _torch_cuda = torch.cuda.is_available()
    _torch_cuda_version = (torch.version.cuda or '').split('.')[0] if torch.version.cuda else ''
except Exception:
    _torch_cuda = False
    _torch_cuda_version = ''

_nvcc_major = _detect_nvcc_version()

ext_modules = []
if _torch_cuda and _torch_cuda_version and _nvcc_major == _torch_cuda_version:
    # Match: build the CUDA extension.
    from torch.utils.cpp_extension import CUDAExtension
    ext_modules.append(
        CUDAExtension('difflogic_cuda', [
            'difflogic/cuda/difflogic.cpp',
            'difflogic/cuda/difflogic_kernel.cu',
        ], extra_compile_args={'nvcc': ['-lineinfo']})
    )
elif _torch_cuda:
    # Mismatch: torch sees CUDA runtime but no matching nvcc toolchain.
    # Skip CUDAExtension; users get implementation='python' (pure PyTorch) only.
    import warnings
    warnings.warn(
        f'difflogic fork: torch CUDA runtime ({_torch_cuda_version}.x) does not match '
        f'system CUDA Toolkit ({_nvcc_major or "missing"}).x — skipping CUDAExtension build, '
        'falling back to implementation="python". '
        'See SL-12 notebook for the RECOVERABLE-LOCAL fork rationale.'
    )

with open('README.md', 'r', encoding='utf-8') as fh:
    long_description = fh.read()

setup(
    name='difflogic',
    version='0.1.0',
    author='Felix Petersen',
    author_email='ads0600@felix-petersen.de',
    long_description=long_description,
    long_description_content_type='text/markdown',
    url='https://github.com/Felix-Petersen/difflogic',
    classifiers=[
        'Programming Language :: Python :: 3',
        'License :: OSI Approved :: MIT License',
        'Operating System :: OS Independent',
        'Topic :: Scientific/Engineering',
        'Topic :: Scientific/Engineering :: Mathematics',
        'Topic :: Scientific/Engineering :: Artificial Intelligence',
        'Topic :: Software Development',
        'Topic :: Software Development :: Libraries',
        'Topic :: Software Development :: Libraries :: Python Modules',
    ],
    package_dir={'difflogic': 'difflogic'},
    packages=['difflogic'],
    ext_modules=ext_modules,
    cmdclass={'build_ext': BuildExtension},
    python_requires='>=3.6',
    install_requires=[
        'torch>=1.6.0',
        'numpy',
    ],
)
