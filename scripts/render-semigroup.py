#!/usr/bin/env python3
"""Render the README animation (requires NumPy, Pillow, and Matplotlib).

Run from the repository root: python3 scripts/render-semigroup.py
Multiplier and jump rates: https://arxiv.org/html/2606.02847#S1.E1.
Both cycles start with a unit point mass at 0. Disk areas encode site masses.
All positive-mass disks have the same color. Straight arrows encode the sign
and magnitude of q(y-x)(p(x)-p(y)); width and darkness use one fixed logarithmic
scale across both sizes and all frames. Flows below display resolution are
omitted; arrowheads are omitted on faint or very short visible segments.
All transfers enter the actual dynamics and energy calculation.
The graph shows Ent_pi(rho_t) / E_n(sqrt(rho_t)), rho_t = n p_t.
It is a numerical illustration, not a proof. The equilibrium ratio is 0/0;
the plotted finite-time ratios approach 2. Playback slows the early evolution
by sampling mathematical time nonuniformly; graph markers show the common time.
"""

from math import cos, hypot, log, log1p, pi, sin
from pathlib import Path

import numpy as np
from matplotlib.backends.backend_agg import FigureCanvasAgg
from matplotlib.figure import Figure
from matplotlib.lines import Line2D
from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
SIZES = (6, 25)
DIAGRAM_WIDTH, PLOT_WIDTH, HEIGHT = 720, 500, 430
WIDTH = DIAGRAM_WIDTH + PLOT_WIDTH
END_TIME = 7.0
FRAME_COUNT = 300
FRAME_DURATION_MS = 70
SCALE = 4
EXPORT_SCALE = 2
RING_RADIUS = 123
MASS_RADIUS = 30
CENTERS = ((180, 203), (540, 203))
WHITE = (255, 255, 255)
INK = (31, 41, 55)
GUIDE = (196, 204, 213)
BLUE = (21, 53, 75)
FLOW_COLOR = (213, 94, 0)
PLOT_COLORS = ("#0072b2", "#d55e00")
PLOT_STYLES = ("-", (0, (5, 3)))
PLOT_MARKERS = ("o", "D")
FLOW_REFERENCE = 0.0001
MIN_FLOW_VISIBILITY = 0.15


class HeatEvolution:
    def __init__(self, n):
        self.n = n
        k = np.arange(n)
        self.spectrum = np.minimum(k, n - k)
        self.rates = np.zeros(n)
        for r in range(1, n):
            # Exact zeros and reflection symmetry; avoid cancellation for even n.
            if n % 2 == 0:
                if r % 2:
                    self.rates[r] = 1 / (n * sin(pi * min(r, n - r) / n) ** 2)
            else:
                self.rates[r] = (1 - cos(2 * pi * (n // 2) * r / n)) / (
                    n * (1 - cos(2 * pi * r / n)))
        self.x, self.y = np.triu_indices(n, 1)
        self.pair_rates = self.rates[(self.y - self.x) % n]

    def distribution(self, t):
        if t == 0:
            p = np.zeros(self.n)
            p[0] = 1.0
            return p
        p = np.fft.ifft(np.exp(-t * self.spectrum)).real
        assert p.min() > -1e-13
        return np.maximum(p, 0)

    def entropy_energy(self, p):
        """Relative entropy and the Dirichlet energy of the square-root density."""
        rho = self.n * p / p.sum()
        u = rho - 1
        centered_entropy = np.zeros(self.n)
        zero = rho == 0
        near = (np.abs(u) < 0.05) & ~zero
        far = ~(zero | near)
        centered_entropy[zero] = 1
        centered_entropy[far] = rho[far] * np.log1p(u[far]) - u[far]
        for k in range(2, 25):
            centered_entropy[near] += (-1) ** k * u[near] ** k / (k * (k - 1))
        entropy = float(centered_entropy.mean())
        roots = np.sqrt(rho)
        denominator = roots[self.x] + roots[self.y]
        difference = np.divide(rho[self.x] - rho[self.y], denominator,
                               out=np.zeros_like(denominator), where=denominator > 0)
        energy = float(np.sum(self.pair_rates * difference ** 2) / self.n)
        return entropy, energy

    def ratio(self, t):
        entropy, energy = self.entropy_energy(self.distribution(t))
        assert energy > 0  # Undefined at exact equilibrium.
        return entropy / energy

    def net_flows(self, p):
        return self.pair_rates * (p[self.x] - p[self.y])


MODELS = tuple(HeatEvolution(n) for n in SIZES)
MAX_FLOW = max(float(model.rates.max()) for model in MODELS)
FLOW_LOG_SCALE = log1p(MAX_FLOW / FLOW_REFERENCE)


def check_distribution(model, p):
    assert abs(p.sum() - 1) < 1e-12
    assert p.min() >= 0
    assert p.max() <= p[0] + 1e-12
    assert np.max(np.abs(p[1:] - p[:0:-1])) < 1e-12


def check_model(model):
    n = model.n
    assert abs(model.rates.sum() - model.spectrum.mean()) < 1e-11
    if n % 2 == 0:
        assert np.all(model.rates[::2] == 0)
    p = model.distribution(0.7)
    derivative = np.fft.ifft(-model.spectrum * np.exp(-0.7 * model.spectrum)).real
    flows = model.net_flows(p)
    incoming = np.zeros(n)
    np.add.at(incoming, model.x, -flows)
    np.add.at(incoming, model.y, flows)
    assert np.max(np.abs(derivative - incoming)) < 1e-12
    assert abs(incoming.sum()) < 1e-12
    a, b = model.distribution(0.3), model.distribution(0.8)
    convolution = np.fft.ifft(np.fft.fft(a) * np.fft.fft(b)).real
    assert np.max(np.abs(convolution - model.distribution(1.1))) < 1e-12
    for t in (0, 0.0001, 0.01, 0.7, 2, END_TIME):
        p = model.distribution(t)
        check_distribution(model, p)
        entropy, energy = model.entropy_energy(p)
        f = np.sqrt(n * p / p.sum())
        fourier_energy = np.sum(model.spectrum * np.abs(np.fft.fft(f) / n) ** 2)
        assert abs(energy - fourier_energy) < 1e-11
        positive = p > 0
        direct_entropy = np.sum(p[positive] * np.log(n * p[positive]))
        assert abs(entropy - direct_entropy) < 1e-12
    initial_ratio = n * log(n) / model.spectrum.sum()
    assert abs(model.ratio(0) - initial_ratio) < 1e-12
    ratios = np.array([model.ratio(t) for t in np.linspace(0, END_TIME, 1001)])
    assert np.all((ratios > 0) & (ratios < 2))
    assert np.all(np.diff(ratios) >= 0)
    assert 0 < 2 - ratios[-1] < 1e-6
    print(f"n={n}: R(0)={ratios[0]:.10f}, R({END_TIME:g})={ratios[-1]:.10f}")


class RatioPlot:
    def __init__(self):
        self.times = END_TIME * np.linspace(0, 1, 500) ** 2
        self.figure = Figure(figsize=(PLOT_WIDTH / 100, HEIGHT / 100), dpi=100 * SCALE)
        self.canvas = FigureCanvasAgg(self.figure)
        axes = self.figure.add_axes((0.13, 0.21, 0.81, 0.65))
        axes.set_xlim(0, END_TIME)
        axes.set_ylim(0, 2.22)
        axes.set_xticks((0, 2, 4, 6))
        axes.set_yticks((0, 1, 2))
        axes.set_xlabel(r"$t$", fontsize=16, color="#39424d", labelpad=8)
        axes.set_title(r"$R_n(t)$", fontsize=18, color="#39424d", pad=14)
        axes.spines[["top", "right"]].set_visible(False)
        for edge in ("left", "bottom"):
            axes.spines[edge].set_color("#b9c1ca")
        axes.tick_params(colors="#59616d", labelsize=12, width=0.7, length=3)
        axes.axhline(2, color="#67727e", linewidth=1.3, linestyle=":", zorder=1)
        self.curves = []
        legend_handles = []
        for model, color, style, shape in zip(MODELS, PLOT_COLORS, PLOT_STYLES, PLOT_MARKERS):
            ratios = np.array([model.ratio(t) for t in self.times])
            axes.plot(self.times, ratios, color=color, alpha=0.20, linewidth=1.8,
                      linestyle=style, zorder=2)
            trail, = axes.plot([], [], color=color, linewidth=2.6, linestyle=style, zorder=3,
                               label=rf"$n={model.n}$")
            marker, = axes.plot([], [], marker=shape, linestyle="none", color=color,
                                markersize=7.5, markerfacecolor=color if shape == "o" else "none",
                                markeredgecolor=color, markeredgewidth=1.4,
                                clip_on=False, zorder=4)
            self.curves.append((model, ratios, trail, marker))
            legend_handles.append(Line2D([], [], color=color, linestyle=style, linewidth=2.6,
                                         marker=shape, markersize=6,
                                         markerfacecolor=color if shape == "o" else "none",
                                         label=rf"$n={model.n}$"))
        axes.legend(handles=legend_handles, loc="lower right", frameon=False,
                    fontsize=12, handlelength=2.4)

    def render(self, t):
        mask = self.times < t
        for model, ratios, trail, marker in self.curves:
            ratio = model.ratio(t)
            trail.set_data(np.append(self.times[mask], t), np.append(ratios[mask], ratio))
            marker.set_data([t], [ratio])
        self.canvas.draw()
        return Image.frombuffer("RGBA", self.canvas.get_width_height(),
                                self.canvas.buffer_rgba(), "raw", "RGBA", 0, 1).convert("RGB")


def mix(a, b, fraction):
    return tuple(round(x + (y - x) * fraction) for x, y in zip(a, b))


def sites(n, center):
    return [(center[0] + RING_RADIUS * sin(2 * pi * k / n),
             center[1] - RING_RADIUS * cos(2 * pi * k / n)) for k in range(n)]


def font(size):
    for candidate in ("DejaVuSans.ttf", "/System/Library/Fonts/Supplemental/Arial.ttf"):
        try:
            return ImageFont.truetype(candidate, size * SCALE)
        except OSError:
            pass
    return ImageFont.load_default(size=size * SCALE)


def render(t, ratio_plot=None):
    image = Image.new("RGB", (WIDTH * SCALE, HEIGHT * SCALE), WHITE)
    draw = ImageDraw.Draw(image)

    def line(points, color, width=1):
        draw.line([(round(x * SCALE), round(y * SCALE)) for x, y in points],
                  fill=color, width=max(1, round(width * SCALE)))

    def disk(point, radius, fill, outline=None, width=1):
        x, y = point
        draw.ellipse([(round((x - radius) * SCALE), round((y - radius) * SCALE)),
                      (round((x + radius) * SCALE), round((y + radius) * SCALE))],
                     fill=fill, outline=outline, width=max(1, round(width * SCALE)))

    def label(text, x, y, size=22):
        draw.text((x * SCALE, y * SCALE), text, font=font(size), fill=INK, anchor="mm")

    for model, center in zip(MODELS, CENTERS):
        p = model.distribution(t)
        check_distribution(model, p)
        locations = sites(model.n, center)
        radii = MASS_RADIUS * np.sqrt(p)
        disk(center, RING_RADIUS, None, GUIDE, 0.8)
        label(f"n = {model.n}", center[0], 394, size=24)
        signed_flows = model.net_flows(p)
        # Faint transfers first, so stronger transfers remain visible at crossings.
        for index in np.argsort(np.abs(signed_flows)):
            flow = float(signed_flows[index])
            visibility = log1p(abs(flow) / FLOW_REFERENCE) / FLOW_LOG_SCALE
            if visibility < MIN_FLOW_VISIBILITY:
                continue
            x, y = int(model.x[index]), int(model.y[index])
            if flow < 0:
                x, y = y, x
            start, end = locations[x], locations[y]
            distance = hypot(end[0] - start[0], end[1] - start[1])
            ux, uy = (end[0] - start[0]) / distance, (end[1] - start[1]) / distance
            start_margin, end_margin = max(1.4, radii[x]) + 0.4, max(1.4, radii[y]) + 0.7
            available = distance - start_margin - end_margin
            if available < 2:
                continue
            a = (start[0] + ux * start_margin, start[1] + uy * start_margin)
            b = (end[0] - ux * end_margin, end[1] - uy * end_margin)
            color = mix(WHITE, FLOW_COLOR, visibility ** 0.6)
            width = 0.65 + 4 * visibility
            line([a, b], color, width)
            if visibility >= 0.30 and available >= 15:
                length = 4 + 5 * visibility
                half_width = 2 + 1.5 * visibility
                arrow = [b, (b[0] - ux * length - uy * half_width,
                              b[1] - uy * length + ux * half_width),
                         (b[0] - ux * length + uy * half_width,
                          b[1] - uy * length - ux * half_width)]
                draw.polygon([(round(x * SCALE), round(y * SCALE)) for x, y in arrow], fill=color)
        # Draw smaller disks first to keep the concentrated mass easy to follow.
        for index in np.argsort(p):
            if p[index] < 1e-12:
                disk(locations[index], 1.4 if model.n > 10 else 3.2, WHITE, GUIDE, 0.7)
            else:
                disk(locations[index], radii[index], BLUE, mix(BLUE, INK, 0.2), 0.6)

    image.paste((ratio_plot or RatioPlot()).render(t), (DIAGRAM_WIDTH * SCALE, 0))
    return image.resize((WIDTH * EXPORT_SCALE, HEIGHT * EXPORT_SCALE), Image.Resampling.LANCZOS)


def main():
    for model in MODELS:
        check_model(model)
    output = ROOT / "assets"
    output.mkdir(exist_ok=True)
    ratio_plot = RatioPlot()
    times = END_TIME * np.linspace(0, 1, FRAME_COUNT) ** 2
    render(0.7, ratio_plot).save(output / "word-length-semigroup.png", optimize=True)
    sample_indices = (0, 30, 70, 130, 210, FRAME_COUNT - 1)
    exported_width, exported_height = WIDTH * EXPORT_SCALE, HEIGHT * EXPORT_SCALE
    sample = Image.new("RGB", (exported_width, exported_height * len(sample_indices)), WHITE)
    for row, i in enumerate(sample_indices):
        sample.paste(render(float(times[i]), ratio_plot), (0, row * exported_height))
    palette = sample.quantize(colors=256, method=Image.Quantize.MEDIANCUT)
    colors = palette.getpalette()
    white_index = max(range(256), key=lambda i: sum(colors[3 * i:3 * i + 3]))
    colors[3 * white_index:3 * white_index + 3] = WHITE
    palette.putpalette(colors)
    # Generate frames incrementally rather than retaining all high-resolution RGB frames.
    def indexed_frames():
        for t in times:
            frame = render(float(t), ratio_plot)
            indexed_frame = frame.quantize(palette=palette, dither=Image.Dither.NONE)
            white_mask = frame.convert("L").point(lambda value: 255 if value == 255 else 0)
            indexed_frame.paste(white_index, mask=white_mask)
            yield indexed_frame

    frames = indexed_frames()
    first = next(frames)
    durations = [FRAME_DURATION_MS] * FRAME_COUNT
    durations[0], durations[-1] = 1000, 3000
    destination = output / "word-length-semigroup.gif"
    first.save(destination, save_all=True, append_images=frames,
                    duration=durations, loop=0, disposal=1, optimize=True)
    with Image.open(destination) as result:
        assert result.n_frames > 200 and result.info.get("loop") == 0
        assert result.size == (exported_width, exported_height)
    print(f"Created {destination.relative_to(ROOT)} ({destination.stat().st_size:,} bytes)")
    print(f"Loop duration: {sum(durations) / 1000:.2f} seconds")
    print("Checked both evolutions, flow directions, conservation, and entropy/energy ratios.")


if __name__ == "__main__":
    main()
