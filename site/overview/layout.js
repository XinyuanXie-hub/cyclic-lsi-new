(() => {
  const root = document.documentElement;
  const frame = document.getElementById('page-frame');
  const page = document.getElementById('readme');
  const layout = document.getElementById('layout');
  const hint = document.getElementById('layout-hint');

  function fitPage() {
    if (root.dataset.layout === 'reading') {
      frame.style.removeProperty('height');
      page.style.removeProperty('--page-scale');
      hint.textContent = 'Text wraps to fit your screen. Choose Desktop proportions to scale the whole page together.';
      return;
    }

    // Keep one desktop layout, scaling text, math, spacing and both figures together.
    const scale = Math.min(1, frame.clientWidth / page.offsetWidth);
    page.style.setProperty('--page-scale', scale);
    frame.style.height = `${page.offsetHeight * scale}px`;
    hint.textContent = 'The whole page scales to fit. Pinch to zoom, or choose Reading view for larger text.';
  }

  function setLayout() {
    root.dataset.layout = layout.value;
    fitPage();
  }

  setLayout();
  document.querySelector('.layout-control').hidden = false;
  hint.hidden = false;
  layout.addEventListener('change', setLayout);
  window.addEventListener('resize', fitPage);

  // Math typesetting, font loading and images can change the unscaled page height.
  if ('ResizeObserver' in window) new ResizeObserver(fitPage).observe(page);
  window.addEventListener('load', fitPage);
})();
