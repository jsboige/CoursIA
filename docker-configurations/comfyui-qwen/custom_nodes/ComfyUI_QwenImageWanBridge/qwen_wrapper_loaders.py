"""
Qwen Wrapper Loaders for ComfyUI
=====================================

This module provides loader classes for Qwen-based image editing workflows.
"""

import torch
import logging
from typing import Dict, Any, Optional, Tuple
from pathlib import Path

import folder_paths
import comfy.model_management as mm
from comfy.utils import load_torch_file
import comfy.model_base

from ComfyUI_QwenImageWanBridge.nodes.qwen_wrapper_base import QwenWrapperBase

logger = logging.getLogger(__name__)

class QwenVLCLIPLoader(QwenWrapperBase):
    """
    CLIP Loader node for Qwen Vision Language Model workflows.
    
    This node provides CLIP model loading capabilities
    for Qwen-based image editing pipelines.
    """
    
    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "clip_name": (folder_paths.get_filename_list("clip"), {}),
            },
            "optional": {
                "device": (["cpu", "cuda", "cuda:1", "cuda:2"], {"default": "cuda"}),
            }
        }
    
    RETURN_TYPES = ("CLIP",)
    RETURN_NAMES = ("clip",)
    FUNCTION = "load_clip"
    CATEGORY = "Qwen/Loaders"
    DESCRIPTION = "Load CLIP model for Qwen workflows"
    
    def __init__(self):
        super().__init__()
        self.clip = None
        
    def load_clip(self, clip_name, device="cuda"):
        """
        Load CLIP model from name.
        
        Args:
            clip_name: Name of the CLIP model
            device: Device to load the model on
            
        Returns:
            Tuple containing the loaded CLIP model
        """
        try:
            logger.info(f"Loading CLIP model: {clip_name}")
            
            # Get the full path to the model
            model_path = folder_paths.get_full_path("clip", clip_name)
            
            if not model_path or not Path(model_path).exists():
                raise FileNotFoundError(f"CLIP model not found: {clip_name}")
            
            # Load the CLIP model
            self.clip = mm.load_torch_file(model_path)
            
            logger.info(f"✅ CLIP model loaded successfully")
            return (self.clip,)
            
        except Exception as e:
            logger.error(f"❌ Failed to load CLIP model: {e}")
            raise
    
    def unload(self):
        """Unload the CLIP model from memory"""
        if self.clip is not None:
            del self.clip
            self.clip = None
            mm.soft_empty_cache()
            logger.info("🗑️ CLIP model unloaded")