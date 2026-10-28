#!/usr/bin/env python3
"""Render the README illustration (requires Pillow and Matplotlib).

Run from the repository root: python3 scripts/render-semigroup.py
The distribution is computed from the Fourier multiplier in the paper,
https://arxiv.org/html/2606.02847#S1.E1. Disk areas encode probabilities.
Straight segments connect pairs of sites. Their darkness increases with the
absolute net transfer rate q(y-x) |p(x)-p(y)| on a fixed square-root scale;
zero transfer is white. The equilibrium panel is the infinite-time limit.
The synchronized plot shows Ent_pi(rho_t) / E_n(sqrt(rho_t)), rho_t = n p_t.
It is a numerical illustration of this trajectory, not a proof of the bound.
"""

from math import cos, exp, fsum, log, log1p, pi, sin, sqrt
from pathlib import Path

from matplotlib.backends.backend_agg import FigureCanvasAgg
from matplotlib.figure import Figure
from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
N = 9
DIAGRAM_WIDTH, PLOT_WIDTH, HEIGHT = 960, 440, 390
WIDTH = DIAGRAM_WIDTH + PLOT_WIDTH
END_TIME = 7
SCALE = 2
RING_RADIUS = 108
MASS_RADIUS = 45
CENTERS = [(160, 181), (480, 181), (800, 181)]
WHITE = (255, 255, 255)
INK = (57, 66, 77)
GUIDE = (175, 184, 193)
BLUE = (67, 126, 168)
FLOW_BLUE = (29, 93, 145)
PALE_BLUE = (221, 233, 241)
ORANGE = (218, 104, 43)


def distribution(t):
    if t == 0:
        return [1.0] + [0.0] * (N - 1)
    values = [
        fsum(exp(-t * min(k, N - k)) * cos(2 * pi * k * x / N)
             for k in range(N)) / N
        for x in range(N)
    ]
    assert min(values) > -1e-12
    return [max(0.0, value) for value in values]


def jump_rate(r):
    return (1 - cos(2 * pi * (N // 2) * r / N)) / (N * (1 - cos(2 * pi * r / N)))


def entropy_energy(p):
    """Relative entropy of the mass distribution and energy of sqrt(n p)."""
    rho = [N * value / fsum(p) for value in p]

    def centered_entropy(value):
        u = value - 1
        if value == 0:
            return 1.0
        if abs(u) < 0.05:
            # (1+u) log(1+u) - u, without cancellation near equilibrium.
            return fsum((-1) ** k * u ** k / (k * (k - 1)) for k in range(2, 25))
        return value * log1p(u) - u

    entropy = fsum(centered_entropy(value) for value in rho) / N
    roots = [sqrt(value) for value in rho]
    energy = fsum(
        jump_rate(y - x) * ((rho[x] - rho[y]) / (roots[x] + roots[y])) ** 2
        for x in range(N) for y in range(x + 1, N)
        if roots[x] + roots[y] > 0
    ) / N
    return entropy, energy


def entropy_energy_ratio(t):
    entropy, energy = entropy_energy(distribution(t))
    # At exact equilibrium the ratio is undefined (0/0), not equal to 2.
    assert energy > 0
    return entropy / energy


def check_distribution(p):
    assert abs(fsum(p) - 1) < 1e-12
    assert min(p) >= 0
    assert max(p) <= p[0] + 1e-12
    assert max(abs(p[r] - p[-r]) for r in range(1, N)) < 1e-12


def check_model():
    p = distribution(0.7)
    for x in range(N):
        fourier_derivative = -fsum(
            min(k, N - k) * exp(-0.7 * min(k, N - k)) * cos(2 * pi * k * x / N)
            for k in range(N)
        ) / N
        generator = fsum(jump_rate(r) * (p[(x + r) % N] - p[x]) for r in range(1, N))
        assert abs(fourier_derivative - generator) < 1e-12
    a, b, combined = distribution(0.3), distribution(0.8), distribution(1.1)
    for x in range(N):
        assert abs(fsum(a[y] * b[(x - y) % N] for y in range(N)) - combined[x]) < 1e-12

    # Independently compare the jump-form energy with the paper's Fourier form.
    for t in (0, 0.01, 0.7, 2, END_TIME):
        p = distribution(t)
        entropy, energy = entropy_energy(p)
        f = [sqrt(N * value / fsum(p)) for value in p]
        fourier_energy = fsum(
            min(k, N - k) * (
                (fsum(f[x] * cos(2 * pi * k * x / N) for x in range(N)) / N) ** 2
                + (fsum(f[x] * sin(2 * pi * k * x / N) for x in range(N)) / N) ** 2
            ) for k in range(1, N)
        )
        assert abs(energy - fourier_energy) < 1e-12
        direct_entropy = fsum(value * log(N * value) for value in p if value > 0)
        assert abs(entropy - direct_entropy) < 1e-12
    initial_ratio = N * log(N) / fsum(min(k, N - k) for k in range(N))
    assert abs(entropy_energy_ratio(0) - initial_ratio) < 1e-12
    ratios = [entropy_energy_ratio(END_TIME * i / 1000) for i in range(1001)]
    assert all(0 < value < 2 for value in ratios)
    assert all(b >= a for a, b in zip(ratios, ratios[1:]))
    assert 0 < 2 - ratios[-1] < 1e-6


class RatioPlot:
    """A scientific plot with a marker synchronized to the mass distribution."""

    def __init__(self):
        self.times = [END_TIME * (i / 400) ** 2 for i in range(401)]
        self.ratios = [entropy_energy_ratio(t) for t in self.times]
        self.figure = Figure(figsize=(PLOT_WIDTH / 100, HEIGHT / 100), dpi=100 * SCALE)
        self.canvas = FigureCanvasAgg(self.figure)
        axes = self.figure.add_axes((0.14, 0.22, 0.80, 0.64))
        axes.set_xlim(0, END_TIME)
        axes.set_ylim(0, 2.22)
        axes.set_xticks((0, 2, 4, 6))
        axes.set_yticks((0, 1, 2))
        axes.set_xlabel("Time", fontsize=13, color="#39424d", labelpad=8)
        axes.set_title("Entropy / energy", fontsize=15, color="#39424d", pad=14)
        axes.spines[["top", "right"]].set_visible(False)
        for edge in ("left", "bottom"):
            axes.spines[edge].set_color("#afb8c1")
        axes.tick_params(colors="#59616d", labelsize=11, width=0.7, length=3)
        axes.axhline(2, color="#da682b", linewidth=1, linestyle=(0, (4, 4)), zorder=1)
        axes.text(END_TIME, 2.07, "Sharp bound: 2", ha="right", va="bottom",
                  color="#b55626", fontsize=11)
        axes.plot(self.times, self.ratios, color="#dce7ef", linewidth=2, zorder=2)
        self.trail, = axes.plot([], [], color="#437ea8", linewidth=2, zorder=3)
        self.marker, = axes.plot([], [], "o", color="#da682b", markersize=7,
                                markeredgecolor="white", markeredgewidth=0.8,
                                clip_on=False, zorder=4)
        self.readout = self.figure.text(0.54, 0.045, "", ha="center", fontsize=11,
                                        color="#59616d")

    def render(self, t):
        ratio = entropy_energy_ratio(t)
        visible = [(x, y) for x, y in zip(self.times, self.ratios) if x < t]
        visible.append((t, ratio))
        self.trail.set_data([x for x, _ in visible], [y for _, y in visible])
        self.marker.set_data([t], [ratio])
        self.readout.set_text(f"Ratio: {ratio:.6f}")
        self.canvas.draw()
        return Image.frombuffer("RGBA", self.canvas.get_width_height(),
                                self.canvas.buffer_rgba(), "raw", "RGBA", 0, 1).convert("RGB")


def mix(a, b, fraction):
    return tuple(round(x + (y - x) * fraction) for x, y in zip(a, b))


def mass_color(p):
    if p <= 1 / N:
        return mix(PALE_BLUE, BLUE, min(1, p * N))
    return mix(BLUE, ORANGE, ((p - 1 / N) / (1 - 1 / N)) ** 0.45)


def sites(center):
    return [(center[0] + RING_RADIUS * sin(2 * pi * k / N),
             center[1] - RING_RADIUS * cos(2 * pi * k / N)) for k in range(N)]


def font(size):
    for candidate in ("DejaVuSans.ttf", "/System/Library/Fonts/Supplemental/Arial.ttf"):
        try:
            return ImageFont.truetype(candidate, size * SCALE)
        except OSError:
            pass
    return ImageFont.load_default(size=size * SCALE)


def render(t, ratio_plot=None):
    p = distribution(t)
    check_distribution(p)
    image = Image.new("RGB", (WIDTH * SCALE, HEIGHT * SCALE), WHITE)
    draw = ImageDraw.Draw(image)

    def line(points, color, width=1):
        draw.line([(round(x * SCALE), round(y * SCALE)) for x, y in points],
                  fill=color, width=max(1, round(width * SCALE)), joint="curve")

    def disk(point, radius, fill, outline=None, width=1):
        x, y = point
        draw.ellipse([(round((x - radius) * SCALE), round((y - radius) * SCALE)),
                      (round((x + radius) * SCALE), round((y + radius) * SCALE))],
                     fill=fill, outline=outline, width=round(width * SCALE))

    def label(text, x, y, size=21, color=INK):
        draw.text((x * SCALE, y * SCALE), text, font=font(size), fill=color, anchor="mm")

    for center in CENTERS:
        disk(center, RING_RADIUS, None, GUIDE, 1)

    # Draw every pair, weaker flows first. A fixed scale makes frames comparable.
    locations = sites(CENTERS[1])
    flows = sorted((jump_rate(y - x) * abs(p[x] - p[y]), x, y)
                   for x in range(N) for y in range(x + 1, N))
    maximum_flux = max(jump_rate(r) for r in range(1, N))
    for flux, x, y in flows:
        if flux < 1e-12:
            continue
        darkness = sqrt(flux / maximum_flux)
        line([locations[x], locations[y]], mix(WHITE, FLOW_BLUE, darkness), 1.5)

    distributions = [[1.0] + [0.0] * (N - 1), p, [1 / N] * N]
    for center, values in zip(CENTERS, distributions):
        for point, value in zip(sites(center), values):
            if value < 1e-12:
                disk(point, 4.1, WHITE, GUIDE, 1.2)
            else:
                disk(point, MASS_RADIUS * sqrt(value), mass_color(value), mix(mass_color(value), INK, 0.35), 1)

    for x in (320, 640):
        line([(x - 25, 181), (x + 21, 181)], GUIDE, 1.3)
        line([(x + 15, 176), (x + 21, 181), (x + 15, 186)], GUIDE, 1.3)
    for center, text in zip(CENTERS, ("Localized", "Spreading", "Equilibrium")):
        label(text, center[0], 337)
    label(f"t = {t:.2f}", CENTERS[1][0], 367, size=15, color=(89, 97, 109))
    image.paste((ratio_plot or RatioPlot()).render(t), (DIAGRAM_WIDTH * SCALE, 0))
    return image.resize((WIDTH, HEIGHT), Image.Resampling.LANCZOS)


def main():
    check_model()
    output = ROOT / "assets"
    output.mkdir(exist_ok=True)
    count = 150
    ratio_plot = RatioPlot()
    frames = [render(END_TIME * (i / (count - 1)) ** 2, ratio_plot) for i in range(count)]
    poster = render(0.7, ratio_plot)
    poster.save(output / "word-length-semigroup.png", optimize=True)

    # One shared palette avoids color flicker between animation frames.
    sample = Image.new("RGB", (WIDTH, HEIGHT * 6), WHITE)
    for row, i in enumerate((0, 20, 40, 70, 100, 149)):
        sample.paste(frames[i], (0, row * HEIGHT))
    palette = sample.quantize(colors=128, method=Image.Quantize.MEDIANCUT)
    # Preserve the white page background instead of quantizing it to light gray.
    colors = palette.getpalette()
    white_index = max(range(128), key=lambda i: sum(colors[3 * i:3 * i + 3]))
    colors[3 * white_index:3 * white_index + 3] = WHITE
    palette.putpalette(colors)
    indexed = []
    for frame in frames:
        indexed_frame = frame.quantize(palette=palette, dither=Image.Dither.NONE)
        # Pillow's approximate palette lookup can map white to a nearby gray.
        white_mask = frame.convert("L").point(lambda value: 255 if value == 255 else 0)
        indexed_frame.paste(white_index, mask=white_mask)
        indexed.append(indexed_frame)
    durations = [60] * count
    durations[0], durations[-1] = 900, 1600
    destination = output / "word-length-semigroup.gif"
    indexed[0].save(destination, save_all=True, append_images=indexed[1:],
                    duration=durations, loop=0, disposal=1, optimize=True)
    with Image.open(destination) as result:
        assert result.n_frames > 100
        assert result.info.get("loop") == 0
    print(f"Created {destination.relative_to(ROOT)} ({destination.stat().st_size:,} bytes)")
    print("Checked positivity, unit mass, reflection symmetry, generator, and semigroup law.")
    print("Checked entropy, Fourier energy, and the sampled ratio's approach to 2 from below.")


if __name__ == "__main__":
    main()
