"""
ComfyUI-QwenImageWanBridge - Custom nodes for Qwen image processing
"""

# 🔧 CORRECTION CRITIQUE : Remplacement des underscores par des tirets pour correspondre au nom du répertoire physique
from ComfyUI_QwenImageWanBridge.nodes.qwen_wrapper_base import QwenWrapperBase
from ComfyUI_QwenImageWanBridge.nodes.qwen_wrapper_loaders import QwenVLCLIPLoader
from ComfyUI_QwenImageWanBridge.nodes.qwen_wrapper_nodes import QwenImageSamplerNode
from ComfyUI_QwenImageWanBridge.nodes.qwen_t2i_wrapper import QwenTextToImageNode
from ComfyUI_QwenImageWanBridge.nodes.qwen_i2v_wrapper import QwenImageToVideoNode
from ComfyUI_QwenImageWanBridge.nodes.qwen_vll_encoder import QwenVLLEncoder

NODE_CLASS_MAPPINGS = {
    "QwenVLCLIPLoader": QwenVLCLIPLoader,
    "QwenImageSamplerNode": QwenImageSamplerNode,
    "QwenAdvancedSampler": QwenAdvancedSampler,
    "QwenTextToImageNode": QwenTextToImageNode,
    "QwenImageToVideoNode": QwenImageToVideoNode,
    "QwenVLLEncoder": QwenVLLEncoder,
}
__all__ = [
    "QwenWrapperBase",
    "QwenVLCLIPLoader",
    "QwenImageSamplerNode",
    "QwenAdvancedSampler",
    "QwenTextToImageNode",
    "QwenImageToVideoNode",
    "QwenVLLEncoder",
    "NODE_CLASS_MAPPINGS",
]
]
