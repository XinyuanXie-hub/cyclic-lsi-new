#!/usr/bin/env python3
"""Render the README animations (requires NumPy, Pillow, and Matplotlib).

Run from the repository root: python3 scripts/render-semigroup.py
Multiplier and jump rates: https://arxiv.org/html/2606.02847#S1.E1.
Both cycles start with unit point mass at 0. Disk area is proportional to mass.
Hollow background markers keep empty sites visible. Arrows show signed net flow
q(y-x)(p(x)-p(y)). One fixed, continuous logarithmic scale controls their width
and darkness, tending to zero with flow. There are no activation thresholds,
minimum opacities, per-panel scales, or time-dependent fades. Color rounding
alone makes sufficiently small flows invisible. All flows enter the dynamics.

The second GIF shows Ent_pi(rho_t) / E_n(sqrt(rho_t)), rho_t = n p_t. This is a
numerical illustration, not a proof; the finite-time ratio approaches 2, while
the exact equilibrium ratio is 0/0. Both GIFs use the same models, sample times,
and durations. Quadratic time sampling slows the early evolution. Playback
holds the initial frame for five seconds and the final frame for three seconds.
Browsers may start separate GIFs at different times.
"""

from math import cos, hypot, log, log1p, pi, sin
from pathlib import Path

import numpy as np
from matplotlib.backends.backend_agg import FigureCanvasAgg
from matplotlib.figure import Figure
from matplotlib.lines import Line2D
from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
SIZES = (5, 21)
DIAGRAM_WIDTH, DIAGRAM_HEIGHT = 720, 350
PLOT_WIDTH, PLOT_HEIGHT = 560, 290
END_TIME = 11.0
# More samples at 33 fps preserve the roughly 26-second evolution between holds.
FRAME_COUNT = 876
FRAME_DURATION_MS = 30
INITIAL_HOLD_MS = 5000
FINAL_HOLD_MS = 3000
SCALE = 4
EXPORT_SCALE = 2
RING_RADIUS = 123
MASS_RADIUS = 18
SITE_RADIUS = 2.8
ARROW_TIP_GAP = 4.5
CENTERS = ((180, 154), (540, 154))
WHITE = (255, 255, 255)
INK = (31, 41, 55)
GUIDE = (196, 204, 213)
BLUE = (21, 53, 75)
FLOW_COLOR = (191, 73, 4)
PLOT_COLORS = ("#0072b2", "#d55e00")
PLOT_STYLES = ("-", (0, (5, 3)))
PLOT_MARKERS = ("o", "D")
FLOW_REFERENCE = 0.001


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
        self.figure = Figure(figsize=(PLOT_WIDTH / 100, PLOT_HEIGHT / 100), dpi=100 * SCALE)
        self.canvas = FigureCanvasAgg(self.figure)
        axes = self.figure.add_axes((0.14, 0.21, 0.80, 0.73))
        axes.set_xlim(0, END_TIME)
        axes.set_ylim(0, 2.22)
        axes.set_xticks(np.arange(0, END_TIME + 1, 2))
        axes.set_yticks((0, 1, 2))
        axes.set_xlabel(r"$t$", fontsize=16, color="#39424d", labelpad=8)
        axes.set_ylabel(r"$R_n(t)$", fontsize=18, color="#39424d", labelpad=10)
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


def flow_strength(flow):
    """A shared continuous scale: zero flow has zero width and zero opacity."""
    return log1p(abs(flow) / FLOW_REFERENCE) / FLOW_LOG_SCALE


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


def render_heat(t):
    image = Image.new("RGB", (DIAGRAM_WIDTH * SCALE, DIAGRAM_HEIGHT * SCALE), WHITE)
    draw = ImageDraw.Draw(image)

    def line(points, color, width=1):
        draw.line([(round(x * SCALE), round(y * SCALE)) for x, y in points],
                  fill=color, width=max(1, round(width * SCALE)))

    def disk(point, radius, fill, outline=None, width=1):
        x, y = point
        draw.ellipse([(round((x - radius) * SCALE), round((y - radius) * SCALE)),
                      (round((x + radius) * SCALE), round((y + radius) * SCALE))],
                     fill=fill, outline=outline, width=max(1, round(width * SCALE)))

    for model, center in zip(MODELS, CENTERS):
        p = model.distribution(t)
        check_distribution(model, p)
        locations = sites(model.n, center)
        radii = MASS_RADIUS * np.sqrt(p)
        disk(center, RING_RADIUS, None, GUIDE, 0.8)
        draw.text((center[0] * SCALE, 317 * SCALE), f"n = {model.n}",
                  font=font(24), fill=INK, anchor="mm")
        signed_flows = model.net_flows(p)
        # Faint transfers first, so stronger transfers remain visible at crossings.
        for index in np.argsort(np.abs(signed_flows)):
            flow = float(signed_flows[index])
            strength = flow_strength(flow)
            color = mix(WHITE, FLOW_COLOR, strength)
            if color == WHITE:
                continue
            x, y = int(model.x[index]), int(model.y[index])
            if flow < 0:
                x, y = y, x
            start, end = locations[x], locations[y]
            distance = hypot(end[0] - start[0], end[1] - start[1])
            ux, uy = (end[0] - start[0]) / distance, (end[1] - start[1]) / distance
            start_margin = max(SITE_RADIUS, radii[x]) + 0.8
            # Keep arrow tips clear of the vertex circles after downsampling.
            end_margin = max(SITE_RADIUS, radii[y]) + ARROW_TIP_GAP
            available = distance - start_margin - end_margin
            if available < 2:
                continue
            a = (start[0] + ux * start_margin, start[1] + uy * start_margin)
            b = (end[0] - ux * end_margin, end[1] - uy * end_margin)
            length = min(2 + 8 * strength, available * 0.45)
            half_width = 0.35 * length
            base = (b[0] - ux * length, b[1] - uy * length)
            line([a, base], color, 5 * strength)
            arrow = [b, (b[0] - ux * length - uy * half_width,
                          b[1] - uy * length + ux * half_width),
                     (b[0] - ux * length + uy * half_width,
                      b[1] - uy * length - ux * half_width)]
            draw.polygon([(round(x * SCALE), round(y * SCALE)) for x, y in arrow], fill=color)
        # Site markers are a separate backdrop, never a floor on encoded mass.
        for location in locations:
            disk(location, SITE_RADIUS, WHITE, GUIDE, 0.7)
        for index in np.argsort(p):
            if p[index] > 0:
                disk(locations[index], radii[index], BLUE, mix(BLUE, INK, 0.2), 0.6)

    return image.resize((DIAGRAM_WIDTH * EXPORT_SCALE, DIAGRAM_HEIGHT * EXPORT_SCALE),
                        Image.Resampling.LANCZOS)


def check_rendering(times):
    """Guard against a visible jump after the hold and unfinished final arrows."""
    initial = np.asarray(render_heat(0), dtype=float)
    first_step = np.asarray(render_heat(float(times[1])), dtype=float)
    onset_change = float(np.abs(first_step - initial).mean())
    assert onset_change < 0.1, f"Abrupt first-frame change: {onset_change:g}"
    for model in MODELS:
        initial_flows = model.net_flows(model.distribution(0))
        assert sum(mix(WHITE, FLOW_COLOR, flow_strength(float(flow))) != WHITE
                   for flow in initial_flows) == np.count_nonzero(model.rates)
        final_flows = model.net_flows(model.distribution(float(times[-1])))
        assert all(mix(WHITE, FLOW_COLOR, flow_strength(float(flow))) == WHITE
                   for flow in final_flows), "Animation ends with visible flows"
    print(f"First-frame mean RGB change: {onset_change:.6f}; final arrows invisible.")


def export_animation(name, render_frame, times):
    output = ROOT / "assets"
    output.mkdir(exist_ok=True)
    snapshot = render_frame(0.7)
    snapshot.save(output / f"{name}.png", optimize=True)
    # Sample the full evolution even when the animation frame count changes.
    sample_indices = np.linspace(0, len(times) - 1, 8, dtype=int)
    exported_width, exported_height = snapshot.size
    sample = Image.new("RGB", (exported_width, exported_height * len(sample_indices)), WHITE)
    for row, i in enumerate(sample_indices):
        sample.paste(render_frame(float(times[i])), (0, row * exported_height))
    palette = sample.quantize(colors=256, method=Image.Quantize.MEDIANCUT)
    colors = palette.getpalette()
    white_index = max(range(256), key=lambda i: sum(colors[3 * i:3 * i + 3]))
    colors[3 * white_index:3 * white_index + 3] = WHITE
    palette.putpalette(colors)
    # Generate frames incrementally rather than retaining all high-resolution RGB frames.
    def indexed_frames():
        for t in times:
            frame = render_frame(float(t))
            indexed_frame = frame.quantize(palette=palette, dither=Image.Dither.NONE)
            white_mask = frame.convert("L").point(lambda value: 255 if value == 255 else 0)
            indexed_frame.paste(white_index, mask=white_mask)
            yield indexed_frame

    frames = indexed_frames()
    first = next(frames)
    durations = [FRAME_DURATION_MS] * len(times)
    durations[0], durations[-1] = INITIAL_HOLD_MS, FINAL_HOLD_MS
    destination = output / f"{name}.gif"
    first.save(destination, save_all=True, append_images=frames,
                    duration=durations, loop=0, disposal=1, optimize=True)
    with Image.open(destination) as result:
        assert result.n_frames > 200 and result.info.get("loop") == 0
        assert result.size == (exported_width, exported_height)
        saved_durations = []
        for frame_index in range(result.n_frames):
            result.seek(frame_index)
            saved_durations.append(result.info["duration"])
        assert sum(saved_durations) == sum(durations)
        assert saved_durations[0] >= INITIAL_HOLD_MS
        assert saved_durations[-1] >= FINAL_HOLD_MS
    print(f"Created {destination.relative_to(ROOT)} ({destination.stat().st_size:,} bytes)")
    print(f"Loop duration: {sum(durations) / 1000:.2f} seconds")


def main():
    for model in MODELS:
        check_model(model)
    # Keep both artifacts tied to these same models, times, and export durations.
    times = END_TIME * np.linspace(0, 1, FRAME_COUNT) ** 2
    check_rendering(times)
    export_animation("word-length-semigroup", render_heat, times)
    ratio_plot = RatioPlot()

    def render_ratio(t):
        return ratio_plot.render(t).resize((PLOT_WIDTH * EXPORT_SCALE, PLOT_HEIGHT * EXPORT_SCALE),
                                           Image.Resampling.LANCZOS)

    export_animation("entropy-energy-ratio", render_ratio, times)
    print("Checked both evolutions, flow directions, conservation, and entropy/energy ratios.")


if __name__ == "__main__":
    main()
