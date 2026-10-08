/**
 * smt-runner.js
 *
 * Opt-in "Run" button component for SMT-LIBv2 code blocks.
 *
 * Page authors add a placeholder element wherever they want a Run
 * button. The component resolves the code to run in the following
 * order of priority:
 *
 *   1. data-code-selector attribute (CSS selector to any element):
 *
 *        <div class="smt-run" data-code-selector="#my-example"></div>
 *
 *   2. Inline code written directly inside the placeholder. The text
 *      content is used as the code and the placeholder content is
 *      replaced by the button:
 *
 *        <div class="smt-run">
 *        (set-logic QF_LIA)
 *        (declare-const a Int)
 *        (assert (> a 0))
 *        (check-sat)
 *        </div>
 *
 *   3. The nearest previous sibling that is a Sphinx highlight block:
 *
 *        <div class="highlight-smtlib notranslate">...</div>
 *        <div class="smt-run"></div>
 *
 * Code extraction is structure-tolerant: if the source element contains
 * a <pre>, its content is used (with Sphinx .linenos spans stripped);
 * otherwise the element's plain text content is used as-is.
 *
 * Per-button solver URL override:
 *
 *   <div class="smt-run" data-solver-url="../../appjs/index.html"></div>
 *
 * Global configuration (optional, set before this script loads):
 *
 *   <script>window.SMT_SOLVER_URL = '../../appjs/index.html';</script>
 *
 * Public API:
 *
 *   window.SmtRun.init(rootElement)
 *     Re-scans for placeholders (useful for dynamically inserted
 *     content). Defaults to document when no argument is given.
 *
 * Clicking a button opens the solver page in a new tab with the code
 * passed through the URL hash: <solver-url>#smt=<encoded code>.
 */
(function () {
  'use strict';

  var DEFAULT_SOLVER_URL = '../../appjs/index.html';

  var HIGHLIGHT_SELECTOR =
    '.highlight-smtlib, .highlight-smt2, .highlight-smtlib2';

  var PLACEHOLDER_SELECTOR = '.smt-run';

  var PLAY_ICON =
    '<svg viewBox="0 0 24 24" aria-hidden="true">' +
    '<path d="M8 5v14l11-7z"/></svg>';

  // ---------------------------------------------------------------------------
  // Styles (injected once)
  // ---------------------------------------------------------------------------
  function injectStyles() {
    if (document.getElementById('smt-run-styles')) return;
    var style = document.createElement('style');
    style.id = 'smt-run-styles';
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
      '  text-decoration: none;',
      '  transition: background 0.2s;',
      '}',
      '.smt-run-btn:hover { background: #219150; color: #fff; }',
      '.smt-run-btn svg {',
      '  width: 11px; height: 11px;',
      '  fill: currentColor; flex-shrink: 0;',
      '}',
    ].join('\n');
    document.head.appendChild(style);
  }

  // ---------------------------------------------------------------------------
  // Code extraction
  // ---------------------------------------------------------------------------

  /**
   * Extracts plain code text from an arbitrary element.
   *
   * Structure-tolerant: if the element contains a <pre> (Sphinx highlight
   * blocks), its content is used with .linenos spans stripped; otherwise
   * the element's own text content is used as-is.
   */
  function extractCode(el) {
    if (!el) return '';
    var source = el.querySelector('pre') || el;
    var clone = source.cloneNode(true);
    var linenos = clone.querySelectorAll('.linenos');
    for (var i = 0; i < linenos.length; i++) {
      linenos[i].parentNode.removeChild(linenos[i]);
    }
    return (clone.textContent || '').trim();
  }

  /** Finds the nearest previous sibling that is a highlight block. */
  function findPreviousHighlight(placeholder) {
    var el = placeholder.previousElementSibling;
    while (el) {
      if (el.matches && el.matches(HIGHLIGHT_SELECTOR)) return el;
      el = el.previousElementSibling;
    }
    return null;
  }

  /**
   * Resolves the code for a given placeholder.
   *
   * Priority:
   *   1. data-code-selector attribute
   *   2. inline text content of the placeholder itself
   *   3. nearest previous sibling highlight block
   */
  function resolveCode(placeholder) {
    var selector = placeholder.getAttribute('data-code-selector');
    if (selector) {
      var target;
      try {
        target = document.querySelector(selector);
      } catch (e) {
        // Invalid selector: fail silently, no button is rendered
        return '';
      }
      return extractCode(target);
    }

    var inline = (placeholder.textContent || '').trim();
    if (inline) return inline;

    return extractCode(findPreviousHighlight(placeholder));
  }

  // ---------------------------------------------------------------------------
  // Component
  // ---------------------------------------------------------------------------

  /** Upgrades a single placeholder element into a Run button. */
  function upgradePlaceholder(placeholder) {
    // Guard against double initialization
    if (placeholder.getAttribute('data-smt-run-initialized') === 'true') return;

    var code = resolveCode(placeholder);
    if (!code) return;

    var solverUrl =
      placeholder.getAttribute('data-solver-url') ||
      window.SMT_SOLVER_URL ||
      DEFAULT_SOLVER_URL;

    var link = document.createElement('a');
    link.className = 'smt-run-btn';
    link.href = solverUrl + '#smt=' + encodeURIComponent(code);
    link.target = '_blank';
    link.rel = 'noopener';
    link.title = 'Open and run this formula in the CVC5 solver';
    link.innerHTML = PLAY_ICON + ' Run';

    // Replace any inline content with the button. For the selector and
    // previous-sibling cases the placeholder is empty anyway, so this
    // is equivalent to appending.
    placeholder.textContent = '';
    placeholder.appendChild(link);
    placeholder.setAttribute('data-smt-run-initialized', 'true');
  }

  /** Scans a root element for placeholders and upgrades them. */
  function init(root) {
    injectStyles();
    var scope = root || document;
    var placeholders = scope.querySelectorAll(PLACEHOLDER_SELECTOR);
    for (var i = 0; i < placeholders.length; i++) {
      upgradePlaceholder(placeholders[i]);
    }
  }

  // Public API for dynamically inserted content
  window.SmtRun = { init: init };

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function () { init(); });
  } else {
    init();
  }
})();