import sys
import os
from PIL import Image
import statistics

def analyze_image(image_path):
    """
    Analyzes an image to determine if it is likely a 'black' or empty image.
    Returns (is_valid, message, stats)
    """
    if not os.path.exists(image_path):
        return False, f"Image file not found: {image_path}", {}

    try:
        with Image.open(image_path) as img:
            # Convert to grayscale for simpler analysis
            gray_img = img.convert('L')
            pixels = list(gray_img.getdata())
            
            if not pixels:
                return False, "Image has no pixels", {}

            # Calculate statistics
            mean_val = statistics.mean(pixels)
            try:
                variance_val = statistics.variance(pixels)
            except statistics.StatisticsError:
                variance_val = 0 # Handle single pixel case if necessary
            
            min_val = min(pixels)
            max_val = max(pixels)

            stats = {
                "mean": mean_val,
                "variance": variance_val,
                "min": min_val,
                "max": max_val,
                "size": img.size
            }

            # Thresholds
            # A completely black image has mean 0. 
            # A 'broken' VAE output often results in pure black or very dark noise.
            # Let's set a conservative threshold. 
            # Even a dark night scene usually has mean > 5 or variance > 10.
            MEAN_THRESHOLD = 5.0
            VARIANCE_THRESHOLD = 10.0

            if mean_val < MEAN_THRESHOLD:
                return False, f"Image is too dark (Mean: {mean_val:.2f} < {MEAN_THRESHOLD})", stats
            
            if variance_val < VARIANCE_THRESHOLD:
                 return False, f"Image has too little contrast/variance (Variance: {variance_val:.2f} < {VARIANCE_THRESHOLD})", stats

            return True, "Image seems valid (not black/flat)", stats

    except Exception as e:
        return False, f"Error processing image: {str(e)}", {}

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python verify_image_content.py <image_path>")
        sys.exit(1)

    image_path = sys.argv[1]
    print(f"Analyzing: {image_path}")
    
    is_valid, message, stats = analyze_image(image_path)
    
    print("-" * 30)
    print(f"Result: {'PASS' if is_valid else 'FAIL'}")
    print(f"Message: {message}")
    if stats:
        print(f"Stats: Mean={stats['mean']:.2f}, Var={stats['variance']:.2f}, Range=[{stats['min']}, {stats['max']}]")
    print("-" * 30)

    if not is_valid:
        sys.exit(1)
    
    sys.exit(0)