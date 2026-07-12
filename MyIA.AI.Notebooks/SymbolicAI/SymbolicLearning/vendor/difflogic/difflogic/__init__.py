# SL-12 fork: import difflogic_cuda only if it was built (CUDA toolchain
# available and matching torch.version.cuda). Without this guard, the
# unconditional `import difflogic_cuda` raises ImportError on CPU-only or
# mismatched-CUDA-Toolkit installs, even when the user only needs
# `implementation='python'` (pure-PyTorch fallback).
try:
    import difflogic_cuda  # noqa: F401
    _HAS_DIFFLOGIC_CUDA = True
except ImportError:
    _HAS_DIFFLOGIC_CUDA = False

from .difflogic import LogicLayer, GroupSum
from .packbitstensor import PackBitsTensor
from .compiled_model import CompiledLogicNet

