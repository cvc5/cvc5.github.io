/**
 * smt-runner.js
 * Injects a "Run" button into Sphinx SMT-LIBv2 code blocks.
 *
 * Clicking opens the CVC5 solver page in a new tab with the code
 * pre-loaded via the URL hash (#smt=<encoded>).
 *
 * Blocks whose download link href contains ".out." are skipped
 * (they are expected-output panels, not input panels).
 */
(function () {
  var SMT_SOLVER_URL = '../../appjs/index.html';

  var style = document.createElement('style');
  style.textContent = [
    '.smt-run-btn {',
    '  display: inline-flex;',
    '  align-items: center;',
    '  gap: 5px;',
    '  margin-top: 6px;',
    '  padding: 4px 11px;',
    '  background: #27ae60;',
    '  color: #fff;',
    '  border: none;',
    '  border-radius: 4px;',
    '  font-size: 12px;',
    '  font-family: sans-serif;',
    '  cursor: pointer;',
    '  transition: background 0.2s;',
    '  text-decoration: none;',  // when rendered as <a>
    '}',
    '.smt-run-btn:hover { background: #219150; color: #fff; }',
    '.smt-run-btn svg { width: 11px; height: 11px; fill: currentColor; flex-shrink: 0; }',
  ].join('\n');
  document.head.appendChild(style);

  var PLAY_ICON = '<svg viewBox="0 0 24 24"><path d="M8 5v14l11-7z"/></svg>';

  // Strip .linenos spans and return plain SMT text
  function extractCode(highlightDiv) {
    var pre = highlightDiv.querySelector('pre');
    if (!pre) return '';
    var clone = pre.cloneNode(true);
    clone.querySelectorAll('.linenos').forEach(function (el) { el.remove(); });
    return clone.textContent.trim();
  }

  /**
   * Returns true if this highlight block is inside a Sphinx tab panel
   * whose download link href contains ".out."
   */
  function isOutputBlock(highlightDiv) {
    // Walk up to the nearest sphinx-tabs-panel ancestor
    var panel = highlightDiv.closest
      ? highlightDiv.closest('.sphinx-tabs-panel')
      : (function () {
          var el = highlightDiv;
          while (el) {
            if (el.classList && el.classList.contains('sphinx-tabs-panel')) return el;
            el = el.parentElement;
          }
          return null;
        })();

    if (!panel) return false;

    // Look for any download link inside the panel
    var links = panel.querySelectorAll('a.reference.external');
    for (var i = 0; i < links.length; i++) {
      if (links[i].href && links[i].href.indexOf('.out.') !== -1) {
        return true;
      }
    }
    return false;
  }

  function injectButtons() {
    var blocks = document.querySelectorAll(
      '.highlight-smtlib, .highlight-smt2, .highlight-smtlib2'
    );

    blocks.forEach(function (highlight) {
      // Skip if a button was already added
      var next = highlight.nextElementSibling;
      if (next && next.classList.contains('smt-run-btn')) return;

      // Skip output blocks
      if (isOutputBlock(highlight)) return;

      var code = extractCode(highlight);
      if (!code) return;
      if (code.indexOf('check-sat') === -1) return;

      // Encode the code into the URL hash so the solver page can read it
      var url = SMT_SOLVER_URL + '#smt=' + encodeURIComponent(code);

      // Use an <a> so middle-click / Ctrl+click also work naturally
      var btn = document.createElement('a');
      btn.className = 'smt-run-btn';
      btn.href = url;
      btn.target = '_blank';
      btn.rel = 'noopener';
      btn.title = 'Open and run this formula in the CVC5 solver';
      btn.innerHTML = PLAY_ICON + ' Run';

      highlight.insertAdjacentElement('afterend', btn);
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', injectButtons);
  } else {
    injectButtons();
  }
})();