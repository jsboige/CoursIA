"""
Qwen Wrapper Base Classes for ComfyUI
======================================

This module provides base classes and utilities for Qwen-based image editing workflows.
"""

import torch
import logging
from typing import Dict, Any, Optional, Tuple
from pathlib import Path

try:
    import folder_paths
except ImportError:
    # ComfyUI might have different module structure
    try:
        from comfy import folder_paths
    except ImportError:
        # Last resort - try to import from ComfyUI context
        import sys
        import os
        # Add ComfyUI root to path if available
        comfyui_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
        if comfyui_root not in sys.path:
            sys.path.insert(0, comfyui_root)
        try:
            import folder_paths
        except ImportError:
            raise ImportError("Cannot import folder_paths from ComfyUI context")
import comfy.model_management as mm
from comfy.utils import load_torch_file
import comfy.model_base

logger = logging.getLogger(__name__)

# Constants for Qwen VAE channels
QWEN_VAE_CHANNELS = 3

class QwenWrapperBase:
    """
    Base class for all Qwen wrapper nodes.
    
    This class provides common functionality and interface
    for Qwen-based image editing pipeline components.
    """
    
    def __init__(self):
        """Initialize the base wrapper"""
        self.device = mm.get_torch_device()
        self.dtype = mm.unet_dtype()
        logger.info(f"Initialized Qwen wrapper on device: {self.device}")
    
    def get_device(self) -> str:
        """Get the current device"""
        return self.device
    
    def get_dtype(self) -> torch.dtype:
        """Get the current data type"""
        return self.dtype
    
    def to_device(self, tensor: torch.Tensor) -> torch.Tensor:
        """Move tensor to the appropriate device"""
        return tensor.to(self.device).to(self.dtype)
    
    def validate_tensor(self, tensor: torch.Tensor, name: str = "tensor") -> bool:
        """
        Validate that a tensor is properly formatted
        
        Args:
            tensor: Tensor to validate
            name: Name of the tensor for logging
            
        Returns:
            True if valid, False otherwise
        """
        if tensor is None:
            logger.error(f"❌ {name} is None")
            return False
        
        if not isinstance(tensor, torch.Tensor):
            logger.error(f"❌ {name} is not a torch.Tensor")
            return False
        
        if tensor.numel() == 0:
            logger.warning(f"⚠️ {name} is empty")
            return False
        
        logger.debug(f"✅ {name} validation passed: shape={tensor.shape}, dtype={tensor.dtype}")
        return True
    
    def log_tensor_info(self, tensor: torch.Tensor, name: str = "tensor") -> None:
        """
        Log detailed information about a tensor
        
        Args:
            tensor: Tensor to analyze
            name: Name of the tensor for logging
        """
        if tensor is not None:
            logger.info(f"📊 {name}: shape={tensor.shape}, dtype={tensor.dtype}, "
                       f"device={tensor.device}, min={tensor.min().item():.4f}, "
                       f"max={tensor.max().item():.4f}, mean={tensor.mean().item():.4f}")
        else:
            logger.warning(f"⚠️ {name} is None")
    
    @classmethod
    def get_model_info(cls, model_path: str) -> Dict[str, Any]:
        """
        Get information about a model file
        
        Args:
            model_path: Path to the model file
            
        Returns:
            Dictionary with model information
        """
        path = Path(model_path)
        
        if not path.exists():
            return {"error": f"Model file not found: {model_path}"}
        
        stat = path.stat()
        return {
            "path": str(path.absolute()),
            "size_mb": stat.st_size / (1024 * 1024),
            "modified": stat.st_mtime,
            "exists": True
        }
    
    def cleanup(self) -> None:
        """Cleanup resources and memory"""
        if hasattr(self, 'model') and self.model is not None:
            del self.model
            self.model = None
        
        if hasattr(self, 'processor') and self.processor is not None:
            del self.processor
            self.processor = None
        
        mm.soft_empty_cache()
        logger.info("🧹 Qwen wrapper cleanup completed")

class QwenModelLoader:
    """
    Utility class for loading Qwen models
    """
    
    @staticmethod
    def load_qwen_model(model_path: str, device: str = "cuda") -> Any:
        """
        Load a Qwen model from path
        
        Args:
            model_path: Path to the model file
            device: Device to load the model on
            
        Returns:
            Loaded model object
        """
        try:
            logger.info(f"Loading Qwen model from: {model_path}")
            
            # Get full path
            full_path = folder_paths.get_full_path("diffusion_models", model_path)
            
            if not full_path or not Path(full_path).exists():
                raise FileNotFoundError(f"Qwen model not found: {model_path}")
            
            # Load the model using ComfyUI utilities
            model = mm.load_torch_file(full_path)
            
            # Move to device
            if hasattr(model, 'to'):
                model = model.to(device)
            
            logger.info(f"✅ Qwen model loaded successfully on {device}")
            return model
            
        except Exception as e:
            logger.error(f"❌ Failed to load Qwen model: {e}")
            raise
    
    @staticmethod
    def get_available_qwen_models() -> list:
        """
        Get list of available Qwen models
        
        Returns:
            List of available model names
        """
        try:
            models = folder_paths.get_filename_list("diffusion_models")
            qwen_models = [m for m in models if "qwen" in m.lower()]
            
            logger.info(f"Found {len(qwen_models)} Qwen models: {qwen_models}")
            return qwen_models
            
        except Exception as e:
            logger.error(f"❌ Failed to get Qwen models: {e}")
            return []