"""
Regenerate img_101.png — LSTM sigmoid gate diagram (Olah style, v2).

After v1 review: σ was clipped by the box; layout was tight. This v2:
- taller canvas with more vertical breathing room
- σ centered cleanly inside with padding
- clearer data flow: h_{t-1} + x_t -> σ box, σ output -> × with C_{t-1}, × -> C_t
- title caption moved to bottom
"""
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Circle, Ellipse

# Olah blog color palette
YELLOW = '#f9e79f'
PURPLE = '#c39bd3'
BLUE   = '#aed6f1'
PINK   = '#fadbd8'
RED    = '#e74c3c'
BLACK  = '#000000'

fig, ax = plt.subplots(figsize=(4, 2.7), dpi=150)
ax.set_xlim(0, 14)
ax.set_ylim(0, 9)
ax.set_aspect('equal')
ax.axis('off')

# --- Inputs (bottom row): h_{t-1} (purple, left) and x_t (blue, right) ---
h_prev = Circle((2.0, 1.5), 0.7, linewidth=1.0, edgecolor=BLACK,
                facecolor=PURPLE, zorder=3)
ax.add_patch(h_prev)
ax.text(2.0, 1.5, r'$h_{t-1}$', fontsize=10, ha='center', va='center', zorder=4)

x_t = Circle((5.5, 1.5), 0.7, linewidth=1.0, edgecolor=BLACK,
             facecolor=BLUE, zorder=3)
ax.add_patch(x_t)
ax.text(5.5, 1.5, r'$x_t$', fontsize=10, ha='center', va='center', zorder=4)

# --- σ box (middle row) ---
sigma_box = FancyBboxPatch(
    (4.5, 4.5), 2.5, 1.5,
    boxstyle='round,pad=0.02,rounding_size=0.15',
    linewidth=1.2, edgecolor=BLACK, facecolor=YELLOW, zorder=3,
)
ax.add_patch(sigma_box)
ax.text(5.75, 5.25, r'$\sigma$', fontsize=22, ha='center', va='center', zorder=4)

# Arrows from inputs up into σ box
ax.annotate('', xy=(5.0, 4.5), xytext=(2.4, 2.2),
            arrowprops=dict(arrowstyle='->', color=BLACK, lw=1.2))
ax.annotate('', xy=(5.6, 4.5), xytext=(5.5, 2.2),
            arrowprops=dict(arrowstyle='->', color=BLACK, lw=1.2))

# --- Top row: C_{t-1} -> × -> C_t -> h_t ---
c_prev = Ellipse((2.0, 7.2), 2.0, 1.0, linewidth=1.0, edgecolor=BLACK,
                 facecolor=PINK, zorder=3)
ax.add_patch(c_prev)
ax.text(2.0, 7.2, r'$C_{t-1}$', fontsize=11, ha='center', va='center', zorder=4)

# Pointwise multiplication circle (×)
mul = Circle((5.5, 7.2), 0.4, linewidth=1.2, edgecolor=RED,
             facecolor='white', zorder=4)
ax.add_patch(mul)
ax.text(5.5, 7.2, r'$\times$', fontsize=15, ha='center', va='center',
        color=RED, zorder=5)

# Arrow from C_{t-1} to ×
ax.annotate('', xy=(5.1, 7.2), xytext=(3.0, 7.2),
            arrowprops=dict(arrowstyle='->', color=BLACK, lw=1.2))

# Arrow from σ box up to ×
ax.annotate('', xy=(5.5, 6.8), xytext=(6.0, 6.0),
            arrowprops=dict(arrowstyle='->', color=BLACK, lw=1.2))

# C_t (right of ×)
c_t = Ellipse((8.5, 7.2), 1.8, 1.0, linewidth=1.0, edgecolor=BLACK,
              facecolor=PINK, zorder=3)
ax.add_patch(c_t)
ax.text(8.5, 7.2, r'$C_t$', fontsize=11, ha='center', va='center', zorder=4)
ax.annotate('', xy=(7.6, 7.2), xytext=(5.9, 7.2),
            arrowprops=dict(arrowstyle='->', color=BLACK, lw=1.2))

# h_t (far right, top row)
h_t = Circle((12.0, 7.2), 0.7, linewidth=1.0, edgecolor=BLACK,
             facecolor=PURPLE, zorder=3)
ax.add_patch(h_t)
ax.text(12.0, 7.2, r'$h_t$', fontsize=10, ha='center', va='center', zorder=4)
ax.annotate('', xy=(11.3, 7.2), xytext=(9.4, 7.2),
            arrowprops=dict(arrowstyle='->', color=BLACK, lw=1.2))

# Caption at bottom
ax.text(7.0, 0.1, 'Porte sigmoïde (σ) — LSTM forget gate',
        fontsize=10, ha='center', va='bottom', style='italic', color='#555555')

plt.tight_layout(pad=0.2)
out = 'img_101.png'
plt.savefig(out, dpi=150, bbox_inches='tight', facecolor='white')
print(f'OK: wrote {out}')